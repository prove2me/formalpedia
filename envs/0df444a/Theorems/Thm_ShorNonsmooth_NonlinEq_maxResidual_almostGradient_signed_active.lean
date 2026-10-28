-- Prove2me | Theorems.Thm_ShorNonsmooth_NonlinEq_maxResidual_almostGradient_signed_active
-- name    : ShorNonsmooth.NonlinEq.maxResidual_almostGradient_signed_active
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T11:10:09.201141+00:00
-- url     : https://prove2.me/theorems/bc83cd8c-8d15-4289-9d7d-a2b5693a387e
-- title:
--   Every almost gradient is a signed active coordinate gradient with the correct residual sign
-- statement:
--   Near a point where the coordinate functions are continuously differentiable, every almost gradient of the max residual at a non-root point is a signed active coordinate gradient: the sign times the active coordinate equals the max residual, and the almost gradient is that sign times the coordinate gradient.
-- source:
--   Shor (1985), Theorem 3.8 regular case, signed active-gradient decomposition of almost gradients

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual
import Definitions.Def_ShorNonsmooth_AlmostDiff_almostGradients

theorem ShorNonsmooth.NonlinEq.maxResidual_almostGradient_signed_active {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : U ∈ nhds xstar)
    (hψ : ∀ i, ContDiffOn ℝ 1 (ψ i) U) :
    ∃ V ∈ nhds xstar, ∀ x ∈ V, maxResidual ψ x ≠ 0 →
      ∀ g ∈ ShorNonsmooth.AlmostDiff.almostGradients (maxResidual ψ) x,
        ∃ i : Fin n, ∃ σ : ℝ, σ ^ 2 = 1 ∧ g = σ • gradient (ψ i) x ∧
          σ * ψ i x = maxResidual ψ x ∧ |ψ i x| = maxResidual ψ x := by sorry
