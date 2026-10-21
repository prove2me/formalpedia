-- Prove2me | Theorems.Thm_ShorNonsmooth_NonlinEq_maxResidual_differentiable_gradient_active_signed
-- name    : ShorNonsmooth.NonlinEq.maxResidual_differentiable_gradient_active_signed
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T10:13:27.519278+00:00
-- url     : https://prove2.me/theorems/23564de8-d87d-4eed-8b29-0acc461d26db
-- title:
--   The max-residual gradient at a differentiable non-root point is an active signed coordinate gradient
-- statement:
--   Near a point where all ψ_i are continuously differentiable, if the max-residual function is differentiable at a non-root point, then its gradient is either the gradient or the negative gradient of a coordinate that attains the maximum absolute residual there.
-- source:
--   Shor (1985), active-coordinate subgradient structure for max_i |ψ_i|

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual

theorem ShorNonsmooth.NonlinEq.maxResidual_differentiable_gradient_active_signed {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : U ∈ nhds xstar)
    (hψ : ∀ i, ContDiffOn ℝ 1 (ψ i) U) :
    ∃ V ∈ nhds xstar, ∀ y ∈ V, maxResidual ψ y ≠ 0 →
      DifferentiableAt ℝ (maxResidual ψ) y →
        ∃ i, (gradient (maxResidual ψ) y = gradient (ψ i) y ∨
          gradient (maxResidual ψ) y = -gradient (ψ i) y) ∧
          |ψ i y| = maxResidual ψ y := by sorry
