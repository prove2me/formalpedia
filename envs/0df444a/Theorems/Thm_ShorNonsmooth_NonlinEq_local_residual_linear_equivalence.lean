-- Prove2me | Theorems.Thm_ShorNonsmooth_NonlinEq_local_residual_linear_equivalence
-- name    : ShorNonsmooth.NonlinEq.local_residual_linear_equivalence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T09:43:00.584988+00:00
-- url     : https://prove2.me/theorems/da452130-3816-40f7-ac6c-bdcc9fbac9ae
-- title:
--   Local two-sided equivalence between the Euclidean norm and the max residual at a common root with independent gradients
-- statement:
--   Let the smooth functions ψ_i vanish at zero and let their gradients at zero be linearly independent. Then on a sufficiently small ball around zero, the Euclidean norm is bounded above by a positive constant multiple of max_i |ψ_i(y)|, and every |ψ_i(y)| is bounded above by a positive constant multiple of the Euclidean norm.
-- source:
--   Shor (1985), Section 3.5, local linearization used in Theorem 3.9, equations (3.36)-(3.37)

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual

theorem ShorNonsmooth.NonlinEq.local_residual_linear_equivalence {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (h0 : ∀ i, ψ i 0 = 0)
    (hind : LinearIndependent ℝ fun i => gradient (ψ i) (0 : EuclideanSpace ℝ (Fin n))) :
    ∃ η > 0, ∃ a > 0, ∃ M > 0, ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ < η →
      a * ‖y‖ ≤ maxResidual ψ y ∧ ∀ i, |ψ i y| ≤ M * ‖y‖ := by sorry
