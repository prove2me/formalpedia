-- Prove2me | Theorems.Thm_ShorNonsmooth_NonlinEq_stage_orthDir_uniform_lower_bound
-- name    : ShorNonsmooth.NonlinEq.stage_orthDir_uniform_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T11:37:49.527764+00:00
-- url     : https://prove2.me/theorems/a3b9f79f-8359-4e76-9949-1db731c88621
-- title:
--   A uniform positive lower bound for ordered orthogonal directions near zero
-- statement:
--   Under globally C1 coordinate functions whose gradients at zero are independent, there is a positive radius and positive constant such that, whenever every point entering the first k ordered steps lies in that radius, the kth orthogonalized direction has norm at least the constant.
-- source:
--   Shor (1985), proof of Theorem 3.9, uniform denominator bound for the orthogonalization stage

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_orthStage

theorem ShorNonsmooth.NonlinEq.stage_orthDir_uniform_lower_bound {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i))
    (hind : LinearIndependent ℝ fun i => gradient (ψ i) (0 : EuclideanSpace ℝ (Fin n))) :
    ∃ η > 0, ∃ b > 0, ∀ (x : ℕ → EuclideanSpace ℝ (Fin n)) (k : Fin n),
      (∀ j : Fin (k.val + 1), ‖x j.val‖ < η) → b ≤ ‖orthDir ψ x k‖ := by sorry
