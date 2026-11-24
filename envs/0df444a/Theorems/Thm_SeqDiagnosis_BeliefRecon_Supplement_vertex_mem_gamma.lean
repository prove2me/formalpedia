-- Prove2me | Theorems.Thm_SeqDiagnosis_BeliefRecon_Supplement_vertex_mem_gamma
-- name    : SeqDiagnosis.BeliefRecon.Supplement.vertex_mem_gamma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:23:14.889166+00:00
-- url     : https://prove2.me/theorems/aba337ec-1028-49b9-9d10-9cdb057618e2
-- title:
--   Proof of Theorem 2, p. ec13 — if $a_{ii}<a_{ij}$ for all $j\ne i$, the vertex $v_i$ lies in $\Gamma_{it}$ (corrected: "for all j" read as $j\ne i$)
-- statement:
--   Let $\mathcal N=\{0,1,\ldots,N\}$ be the classes, with class densities $f_0,\ldots,f_N$ of the exponential tilting model (2) with respect to a reference measure $\mu$ on the observation space $\mathcal Y$. Let $a_{ij}\ge 0$ be the cost of diagnosing class $j$ when the true class is $i$ and $c_i\ge0$ the per-period delay cost under class $i$. For a belief $\Pi=(\pi_0,\ldots,\pi_N)$ in the simplex $S^N$, the stopping values are $V^j(\Pi)=\sum_i\pi_ia_{ij}$, and for a horizon $T<\infty$ the optimal values $V_t$, $t=0,\ldots,T$, solve
--
--   $$V_T(\Pi)=\min_jV^j(\Pi),\qquad V_t(\Pi)=\min\Bigl\{\min_jV^j(\Pi),\ \sum_i\pi_ic_i+\int_{\mathcal Y}V_{t+1}\bigl(\mathcal B(\Pi,y)\bigr)\,\Pi F(y)\,d\mu(y)\Bigr\},$$
--
--   where $\mathcal B(\Pi,y)_j=\pi_jf_j(y)/\Pi F(y)$ is the Bayesian operator and $\Pi F(y)=\sum_i\pi_if_i(y)$. The second term of the minimum is the waiting value $V^w_t(\Pi)$. The stopping region for class $j$ in period $t$ is $\Gamma_{jt}=\{\Pi\in S^N: V_t(\Pi)=V^j(\Pi)\}$; ties count as stopping.
--
--   Let $v_i$ be the belief state with $\pi_i=1$ and $\pi_j=0$ for $j\ne i$. If
--
--   $$a_{ii}<a_{ij}\quad\text{for all } j\ne i,$$
--
--   then $v_i\in\Gamma_{it}$ for every period $t\le T$: when the true class is known to be $i$, diagnosing $i$ immediately is optimal.
--
--   Together with the convexity of $\Gamma_{it}$ this places the whole segment from any point of $\Gamma_{it}$ to $v_i$ inside $\Gamma_{it}$, which is part 1 of Theorem 2.
--
--   Differences from the source:
--   - reading: class densities f_0,…,f_N on 𝒴 satisfying (2) → the published base Model with M.Standing and M.ETM (f₀ > 0 on Y, ∫ f₀ dμ = 1, measurable densities, integrable tilts); reason: inherited unchanged from the published base mission, where 𝒴 is read as the support of f₀ and each f_i is a probability density; the integrals in (1) need these to be finite
--   - generalization: observations in a set 𝒴 of the real line, integrals dy → observations in any measurable type Y, integrals against the base reference measure μ; reason: specializes to 𝒴 ⊂ ℝ with Lebesgue measure (continuous case) or counting measure (discrete case, which the paper also allows, p. 6)
--   - encoding: V_t, t = 0,…,T, by the optimality equations (1) → value M C T t = valueToGo M C (T − t), the value with T − t periods to go, used only for t ≤ T; reason: backward recursion on the number of periods to go; the same values for every t ≤ T
--   - correction: when aii < aij for all j → a_ii < a_ij for all j ≠ i; reason: typo: at j = i the printed condition reads a_ii < a_ii, which no cost structure satisfies; Theorem 2, part 1 (p. 15) states the condition for all j ≠ i and the proof uses it for j ≠ i
-- source:
--   Wang, Optimal Sequential Multi-class Diagnosis, arXiv:1506.08915v4, p. ec13 (PDF 50), proof of Theorem 2 (EC.5), "vi ∈ Γit for all t"

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Supplement_Value

namespace SeqDiagnosis.BeliefRecon.Supplement

/-- Proof of Theorem 2, p. ec13: if `a_ii < a_ij` for all `j ≠ i`, the vertex `v_i` lies in
`Γ_{it}` for every period `t ≤ T`. -/
theorem vertex_mem_gamma {Y : Type*} [MeasurableSpace Y] {N p : ℕ}
    (M : Model Y N p) (hS : M.Standing) (hETM : M.ETM)
    (C : Costs N) (hC : C.Standing) (T : ℕ) :
    ∀ i : Fin (N + 1), (∀ j, j ≠ i → C.a i i < C.a i j) →
      ∀ t : ℕ, t ≤ T → (Pi.single i 1 : Fin (N + 1) → ℝ) ∈ Gamma M C T t i := by sorry

end SeqDiagnosis.BeliefRecon.Supplement
