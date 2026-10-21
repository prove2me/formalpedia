-- Prove2me | Theorems.Thm_ShorNonsmooth_NonlinEq_maxResidual_almostGradient_active_signed
-- name    : ShorNonsmooth.NonlinEq.maxResidual_almostGradient_active_signed
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T09:51:43.355399+00:00
-- url     : https://prove2.me/theorems/8e5698d8-cc8b-4d35-8637-554c47aefbbd
-- title:
--   Every almost gradient of the max residual is an active signed coordinate gradient
-- statement:
--   Near a point where the smooth coordinate functions are continuously differentiable, every almost gradient of max_i |ψ_i(x)| at a non-root point is either the gradient or the negative gradient of a coordinate ψ_i that attains the maximum absolute residual at x.
-- source:
--   Shor (1985), Theorem 3.8 regular case, active-coordinate structure of almost gradients

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual
import Definitions.Def_ShorNonsmooth_AlmostDiff_almostGradients

theorem ShorNonsmooth.NonlinEq.maxResidual_almostGradient_active_signed {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : U ∈ nhds xstar)
    (hψ : ∀ i, ContDiffOn ℝ 1 (ψ i) U) :
    ∃ V ∈ nhds xstar, ∀ x ∈ V, maxResidual ψ x ≠ 0 →
      ∀ g ∈ ShorNonsmooth.AlmostDiff.almostGradients (maxResidual ψ) x,
        ∃ i, (g = gradient (ψ i) x ∨ g = -gradient (ψ i) x) ∧
          |ψ i x| = maxResidual ψ x := by sorry
