-- Prove2me | Theorems.Thm_StructEstMDP_FiniteTime_display_40
-- name    : StructEstMDP.FiniteTime.display_40
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:26.899989+00:00
-- url     : https://prove2.me/theorems/b01efa7d-1a3e-4171-b1cb-6856180f126d
-- title:
--   Display (40), p. 21 — the gradient estimator is bounded: ‖h(θ; τ) − h(θ; τ′)‖ ≤ 2L_r/(1−γ) = 2L_q
-- statement:
--   Let $\gamma\in[0,1)$ and let the reward satisfy Assumption 3 with constant $L_r$. For a trajectory $\tau=\{(s_t,a_t)\}_{t\ge0}$ let $h(\theta;\tau)=\sum_{t=0}^\infty\gamma^t\nabla_\theta r(s_t,a_t;\theta)$. Then for every $\theta$ and all trajectories $\tau,\tau'$,
--
--   $$\|h(\theta;\tau)-h(\theta;\tau')\|\le2L_r\sum_{t=0}^\infty\gamma^t=\frac{2L_r}{1-\gamma}=2L_q.$$
--
--   Applied to $\tau=\tau^E_{k-1}$ and $\tau'=\tau^A_{k-1}$ this is the bound $\|g_{k-1}\|\le2L_q$ on the stochastic gradient, which controls the drift $\|\theta_k-\theta_{k-1}\|\le2\alpha L_q$ of the reward parameter.
-- source:
--   Zeng, Hong and Garcia, Structural Estimation of Markov Decision Processes in High-Dimensional State Space with Finite-Time Guarantees, arXiv:2210.01282v3, p. 21, display (40), proof of Theorem 1

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_StructEstMDP_FiniteTime_Setting

open FoundationsML.ReinforcementLearning MeasureTheory

namespace StructEstMDP.FiniteTime

/-- Display (40), p. 21: under Assumption 3 the gradient estimator is bounded,
`‖h(θ; τ) − h(θ; τ')‖ ≤ 2L_r ∑_{t≥0} γᵗ = 2L_r/(1−γ) = 2L_q`, for every `θ` and all
trajectories `τ, τ'`. -/
theorem display_40 {S A : Type*} (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {p : ℕ} (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ) (Lr Lg : ℝ)
    (h3 : Assumption3 r Lr Lg)
    (θ : EuclideanSpace ℝ (Fin p)) (τ τ' : Traj S A) :
    ‖hGrad γ r θ τ - hGrad γ r θ τ'‖ ≤ 2 * (Lr / (1 - γ)) := by sorry

end StructEstMDP.FiniteTime
