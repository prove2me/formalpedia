-- Prove2me | Theorems.Thm_StructEstMDP_FiniteTime_display_41
-- name    : StructEstMDP.FiniteTime.display_41
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:17.079234+00:00
-- url     : https://prove2.me/theorems/28cb9a25-ee02-4fa9-862c-60c1dab1d0b8
-- title:
--   Display (41), p. 21 — one-step recursion ‖Q_k − Q_{θ_k}‖_∞ ≤ γ‖Q_{θ_{k−1}} − Q_{k−1}‖_∞ + 2γε/(1−γ) + 4αL_q²
-- statement:
--   Let $(\mathcal S,\mathcal A,P)$ be a finite MDP with discount $\gamma\in[0,1)$, let the reward satisfy Assumption 3 with constant $L_r$, and write $L_q=L_r/(1-\gamma)$. Consider any run of Algorithm 1 with step size $\alpha\ge0$ and policy-evaluation error $\varepsilon$, and let $Q_k$ be the soft Q-function of $(\theta_k,\pi_k)$ and $Q_{\theta_k}$ the soft-optimal Q-function at $\theta_k$. Then for every $k\ge1$ and every realization of the run,
--
--   $$\|Q_k-Q_{\theta_k}\|_\infty\le\gamma\|Q_{\theta_{k-1}}-Q_{k-1}\|_\infty+\frac{2\gamma\varepsilon}{1-\gamma}+4\alpha L_q^2.$$
--
--   This recursion combines the contraction (33), the Lipschitz bounds (20a) and (31), and the bound (40) on the gradient estimator; summed over $k$ it yields the averaged tracking bound after (44).
--
--   **Formalization Note** The inequality holds pathwise, with no expectation; the Lean indexes it as $k+1$ for $k\ge0$.
-- source:
--   Zeng, Hong and Garcia, Structural Estimation of Markov Decision Processes in High-Dimensional State Space with Finite-Time Guarantees, arXiv:2210.01282v3, p. 21, display (41), proof of Theorem 1

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_StructEstMDP_FiniteTime_Setting

open FoundationsML.ReinforcementLearning MeasureTheory

namespace StructEstMDP.FiniteTime

/-- Display (41), p. 21: along every run of Algorithm 1 with step `α ≥ 0` and evaluation error
`ε`, for every `k ≥ 1` and every realization,
`‖Q_k − Q_{θ_k}‖_∞ ≤ γ‖Q_{θ_{k−1}} − Q_{k−1}‖_∞ + 2γε/(1−γ) + 4αL_q²`, where `Q_k` is the
soft Q-function of `(θ_k, π_k)` and `L_q = L_r/(1−γ)`. Stated with `k + 1` in place of `k`. -/
theorem display_41 {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (ρ : S → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {p : ℕ} (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ) (Lr Lg : ℝ)
    (h3 : Assumption3 r Lr Lg)
    {m : ℕ} (D : Fin m → Traj S A)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) (ℱ : Filtration ℕ mΩ)
    (α ε : ℝ) (hα : 0 ≤ α) (θ₀ : EuclideanSpace ℝ (Fin p)) (π₀ : S → A → ℝ)
    (θ : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (π Qhat : ℕ → Ω → S → A → ℝ)
    (τE τA : ℕ → Ω → Traj S A)
    (hrun : IsMLIRLRun P γ ρ r D Pr ℱ α ε θ₀ π₀ θ π Qhat τE τA)
    (k : ℕ) (ω : Ω) :
    supNorm (softQ P γ r (θ (k + 1) ω) (π (k + 1) ω) - optQ P γ r (θ (k + 1) ω)) ≤
      γ * supNorm (optQ P γ r (θ k ω) - softQ P γ r (θ k ω) (π k ω)) +
        2 * γ * ε / (1 - γ) + 4 * α * (Lr / (1 - γ)) ^ 2 := by sorry

end StructEstMDP.FiniteTime
