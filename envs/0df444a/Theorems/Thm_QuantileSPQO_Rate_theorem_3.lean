-- Prove2me | Theorems.Thm_QuantileSPQO_Rate_theorem_3
-- name    : QuantileSPQO.Rate.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:58.310367+00:00
-- url     : https://prove2.me/theorems/3c5f7b4a-182a-4a45-a8ec-0f1a5972dabc
-- title:
--   Theorem 3 — SPQO's mean absolute error E‖θ_k − θ*‖ is O(α_k/γ_k) + O(c_k²) + O(β_k^{1/2}/c_k)
-- statement:
--   Let $(\theta_k,q_k,D_k)$ be a run of Algorithm SPQO on a probability space $(\Omega,P)$ for a black box with $\varphi$-quantile function $q$ on a compact convex constraint set $\Theta\subseteq\mathbb R^d$, $d\ge1$. Assume:
--
--   1. A1, A2, A3 and B1, B2;
--   2. the step sizes of Section 4: $\alpha_k=a/(k+1)^\alpha$, $\beta_k=b/(k+1)^\beta$, $\gamma_k=r/(k+1)^\gamma$, $c_k=c/(k+1)^\tau$ with $a,b,r,c>0$ and exponents in $(0,1)$;
--   3. $q$ is twice continuously differentiable on an open set containing $\Theta$, and $\theta^*$ is a point in the interior of $\Theta$ that is the unique equilibrium of the projected ODE $\dot\theta=-\nabla q(\theta)+z$, $z\in-C(\theta)$ (25): the only $\theta\in\Theta$ with $-\nabla q(\theta)\in C(\theta)$, i.e. with $\nabla q(\theta)^T(\tilde\theta-\theta)\ge0$ for all $\tilde\theta\in\Theta$, is $\theta=\theta^*$;
--   4. B3 at $\theta^*$: the Hessian of $q$ satisfies $v^T\nabla^2q(\theta)v\ge\varrho\|v\|^2$ on every segment $[\theta_k,\theta^*]$, for a constant $\varrho>0$.
--
--   Then
--   $$
--   E\big[\|\theta_k-\theta^*\|\big]=O\Big(\frac{\alpha_k}{\gamma_k}\Big)+O\big(c_k^2\big)+O\Big(\frac{\beta_k^{1/2}}{c_k}\Big).
--   $$
--
--   This is the paper's main rate result, which it describes as the first convergence rate for a three-timescale stochastic approximation algorithm; balancing the three terms selects the step-size exponents.
--
--   **Formalization Note** The conclusion reads: there is a constant $C$, depending on the instance and the run but not on $k$, with $E\|\theta_k-\theta^*\|\le C(\alpha_k/\gamma_k+c_k^2+\beta_k^{1/2}/c_k)$ for all large $k$; the expectation is a Lebesgue integral in $[0,\infty]$. The paper's Section 4 standing assumption (p. 16) that the projected ODE (25) has a unique globally asymptotically stable equilibrium $\theta^*$ in the interior of $\Theta$ is stated through its equivalent first-order form: the equilibria of (25) are exactly the points $\theta\in\Theta$ with $-\nabla q(\theta)$ in the normal cone $C(\theta)$ of (24), and since $q$ is a Lyapunov function for (25) on the compact set $\Theta$, a unique equilibrium is automatically globally asymptotically stable, while a globally asymptotically stable equilibrium is the only equilibrium. Strict convexity of $q$ with an interior minimizer (the sufficient condition of p. 14) is a special case. The quantile recursion is truncated to an interval $I\supseteq q(\Theta)$ as the paper recommends on p. 13 (D1); $I=\mathbb R$ gives the printed (20), but then no run satisfies A1(b) or B1. Further disclosures (first-derivative bound in A1, conditional-marginal sampling model, $\theta_0\in\Theta$, $k+1$ in the step sizes, continuity of $f$ on $\mathbb R\times\Theta$) are listed in the Setting file.
-- source:
--   Hu, Song and Fu, Quantile Optimization via Multiple Timescale Local Search for Black-box Functions, arXiv:2308.07607v1, p. 19, Theorem 3 (27) (standing assumptions pp. 16–17)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_QuantileSPQO_Rate_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace QuantileSPQO.Rate

theorem theorem_3 {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ} (hd : 0 < d)
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (M : Model d) (Θ : Set (E d)) (Proj : E d → E d) (I : Set ℝ) (Pq : ℝ → ℝ)
    (α β γ c : ℕ → ℝ) (R : Run Ω d)
    (hΘ : IsConstraintSet Θ) (hM : IsQuantileModel M Θ)
    (hProj : SpectralProjGrad.Shared.IsProjOnto Θ Proj)
    (hrun : IsSPQORun P ℱ M Θ Proj I Pq α β γ c R)
    (hA1 : A1 P M R) (hA2 : A2 P ℱ R) (hA3a : A3a β c)
    (hA3b : A3b γ) (hA3c : A3c α) (hA3d : A3d α β γ)
    (hB1 : B1 P M R)
    (hB2 : B2 M Θ) (θstar : E d) (hB3 : B3 P M R θstar)
    (hpoly : PolySteps α β γ c)
    (hq2 : ∃ U : Set (E d), IsOpen U ∧ Θ ⊆ U ∧ ContDiffOn ℝ 2 M.qf U)
    (hstar : θstar ∈ interior Θ)
    (hstat : ∀ θ ∈ Θ, (∀ θ' ∈ Θ, 0 ≤ ⟪gradient M.qf θ, θ' - θ⟫) ↔ θ = θstar) :
    ∃ C : ℝ, ∀ᶠ k in atTop,
      ∫⁻ ω, ‖R.θ k ω - θstar‖ₑ ∂P
        ≤ ENNReal.ofReal (C * (α k / γ k + c k ^ 2 + Real.sqrt (β k) / c k)) := by sorry

end QuantileSPQO.Rate
