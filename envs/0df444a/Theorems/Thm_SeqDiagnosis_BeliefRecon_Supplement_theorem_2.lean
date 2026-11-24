-- Prove2me | Theorems.Thm_SeqDiagnosis_BeliefRecon_Supplement_theorem_2
-- name    : SeqDiagnosis.BeliefRecon.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:24:04.134874+00:00
-- url     : https://prove2.me/theorems/7b6e9010-1dc9-4005-8cf0-de7e892971d8
-- title:
--   Theorem 2, p. 15 — $\omega$-convexity of the stopping regions $\Omega_{it}$ (both parts)
-- statement:
--   Let $\mathcal N=\{0,1,\ldots,N\}$ be the classes, with class densities $f_0,\ldots,f_N$ of the exponential tilting model (2) with respect to a reference measure $\mu$ on the observation space $\mathcal Y$. Let $a_{ij}\ge 0$ be the cost of diagnosing class $j$ when the true class is $i$ and $c_i\ge0$ the per-period delay cost under class $i$. For a belief $\Pi=(\pi_0,\ldots,\pi_N)$ in the simplex $S^N$, the stopping values are $V^j(\Pi)=\sum_i\pi_ia_{ij}$, and for a horizon $T<\infty$ the optimal values $V_t$, $t=0,\ldots,T$, solve
--
--   $$V_T(\Pi)=\min_jV^j(\Pi),\qquad V_t(\Pi)=\min\Bigl\{\min_jV^j(\Pi),\ \sum_i\pi_ic_i+\int_{\mathcal Y}V_{t+1}\bigl(\mathcal B(\Pi,y)\bigr)\,\Pi F(y)\,d\mu(y)\Bigr\},$$
--
--   where $\mathcal B(\Pi,y)_j=\pi_jf_j(y)/\Pi F(y)$ is the Bayesian operator and $\Pi F(y)=\sum_i\pi_if_i(y)$. The second term of the minimum is the waiting value $V^w_t(\Pi)$. The stopping region for class $j$ in period $t$ is $\Gamma_{jt}=\{\Pi\in S^N: V_t(\Pi)=V^j(\Pi)\}$; ties count as stopping.
--
--   Let (2) hold, let $\mathbb B=\mathbb R\mathbb P$ be a rank decomposition with $\mathbb R$ of full column rank $r$ and $\mathbb P$ of full row rank $r$, and let $\theta\in S^N$ be the prior. For $t\ge1$ let $\Omega_t$ be the set of attainable diagnostic statistics $x_t$, $\mathcal T^t(x,\theta)$ the reconstructed belief (3), and $\Omega_{it}=\{x\in\Omega_t: V_t(\mathcal T^t(x,\theta))=V^i(\mathcal T^t(x,\theta))\}$ the stopping region for class $i$ in the diagnostic-statistic space. Write $e_j\mathbb Rx$ for row $j$ of $\mathbb Rx$, with $e_0$ the null row. Then:
--
--   1. If $a_{ii}<a_{ij}$ for all $j\ne i$ and $x^a\in\Omega_{it}$ for some $1\le t\le T$, then
--   $$\omega^i_t(x^a)=\{x\in\Omega_t: e_j\mathbb R(x-x^a)=0\ \forall j\ne i\in\mathcal N,\ e_i\mathbb R(x-x^a)>0\}\subseteq\Omega_{it}.$$
--   2. If $x^a,x^b\in\Omega_{it}$ for some $t\ge1$, then for every $s$ with $t\le s\le T$,
--   $$\omega_s(x^a,x^b,t)=\{x\in\Omega_s: \mathcal T^s(x,\theta)=\rho\mathcal T^t(x^a,\theta)+(1-\rho)\mathcal T^t(x^b,\theta),\ \rho\in(0,1)\}\subseteq\Omega_{is}.$$
--
--   The stopping regions in the diagnostic-statistic space need not be convex, but they contain these curves through any of their points; this lets parts of $\Omega_{is}$ be identified without solving the Bellman equations. For $i=0$ the set $\omega^0_t(x^a)$ is empty, because $e_0\mathbb R=0$.
--
--   Differences from the source:
--   - reading: class densities f_0,…,f_N on 𝒴 satisfying (2) → the published base Model with M.Standing and M.ETM (f₀ > 0 on Y, ∫ f₀ dμ = 1, measurable densities, integrable tilts); reason: inherited unchanged from the published base mission, where 𝒴 is read as the support of f₀ and each f_i is a probability density; the integrals in (1) need these to be finite
--   - generalization: observations in a set 𝒴 of the real line, integrals dy → observations in any measurable type Y, integrals against the base reference measure μ; reason: specializes to 𝒴 ⊂ ℝ with Lebesgue measure (continuous case) or counting measure (discrete case, which the paper also allows, p. 6)
--   - encoding: V_t, t = 0,…,T, by the optimality equations (1) → value M C T t = valueToGo M C (T − t), the value with T − t periods to go, used only for t ≤ T; reason: backward recursion on the number of periods to go; the same values for every t ≤ T
--   - encoding: Ωt, 𝒯ᵗ for t ≥ 1 and periods of the horizon; "for some t", "for all s ⩾ t" → 1 ≤ t ≤ T in part 1; 1 ≤ t ≤ s ≤ T in part 2; reason: Ωt and 𝒯ᵗ are defined for t ≥ 1 (Theorem 1) and Ωit for periods of the finite horizon T of §2; no admissible instance is removed
-- source:
--   Wang, Optimal Sequential Multi-class Diagnosis, arXiv:1506.08915v4, p. 15 (PDF 15), Theorem 2; proof in EC.5, pp. ec12–ec13 (PDF 49–50)

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Supplement_Value

namespace SeqDiagnosis.BeliefRecon.Supplement

/-- Theorem 2 (ω-convexity of the stopping regions), both parts, finite horizon `T`. -/
theorem theorem_2 {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (hS : M.Standing) (hETM : M.ETM)
    (R : Matrix (Fin N) (Fin r) ℝ) (P : Matrix (Fin r) (Fin p) ℝ)
    (hRP : M.Bmat = R * P) (hR : R.rank = r) (hP : P.rank = r)
    (θ : Fin (N + 1) → ℝ) (hθ : θ ∈ stdSimplex ℝ (Fin (N + 1)))
    (C : Costs N) (hC : C.Standing) (T : ℕ) :
    (∀ i : Fin (N + 1), (∀ j, j ≠ i → C.a i i < C.a i j) →
      ∀ t : ℕ, 1 ≤ t → t ≤ T → ∀ xa ∈ OmegaStop M C R P θ T t i,
        omegaVertex M R P t i xa ⊆ OmegaStop M C R P θ T t i) ∧
    (∀ (i : Fin (N + 1)) (t : ℕ), 1 ≤ t →
      ∀ xa ∈ OmegaStop M C R P θ T t i, ∀ xb ∈ OmegaStop M C R P θ T t i,
        ∀ s : ℕ, t ≤ s → s ≤ T →
          omegaCurve M R P θ s t xa xb ⊆ OmegaStop M C R P θ T s i) := by sorry

end SeqDiagnosis.BeliefRecon.Supplement
