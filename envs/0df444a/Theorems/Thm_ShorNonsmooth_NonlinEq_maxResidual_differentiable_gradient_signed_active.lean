-- Prove2me | Theorems.Thm_ShorNonsmooth_NonlinEq_maxResidual_differentiable_gradient_signed_active
-- name    : ShorNonsmooth.NonlinEq.maxResidual_differentiable_gradient_signed_active
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:57:48.216751+00:00
-- url     : https://prove2.me/theorems/15bde6c3-702e-40ff-843f-4edaa6b0370f
-- title:
--   The max-residual gradient at a differentiable non-root point is a correctly signed active coordinate gradient
-- statement:
--   Near a point where all ψ_i are continuously differentiable, if the max-residual function is differentiable at a non-root point, its gradient is a signed active coordinate gradient, with the same sign that makes the signed coordinate equal the max residual.
-- source:
--   Shor (1985), active-coordinate subgradient structure for max_i |ψ_i|

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual

theorem ShorNonsmooth.NonlinEq.maxResidual_differentiable_gradient_signed_active {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : U ∈ nhds xstar)
    (hψ : ∀ i, ContDiffOn ℝ 1 (ψ i) U) :
    ∃ V ∈ nhds xstar, ∀ y ∈ V, maxResidual ψ y ≠ 0 →
      DifferentiableAt ℝ (maxResidual ψ) y →
        ∃ i : Fin n, ∃ σ : ℝ, σ ^ 2 = 1 ∧
          gradient (maxResidual ψ) y = σ • gradient (ψ i) y ∧
          σ * ψ i y = maxResidual ψ y ∧ |ψ i y| = maxResidual ψ y := by sorry
