-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_covariance_le_regularized_of_quadratic_shift
-- name    : WeilDefect.MarkerStability.covariance_le_regularized_of_quadratic_shift
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T20:19:44.545935+00:00
-- url     : https://prove2.me/theorems/45686223-f451-4ef1-8b97-9164a140179b
-- title:
--   Quadratic semibound gives covariance order above an explicit shift
-- statement:
--   On the same complete complex Hilbert spaces, a self-adjoint covariance A and synthesis N satisfying Re⟨Ax,x⟩−‖N* x‖² ≥ −k‖x‖² on every vector obey NN* ≤ A+ε I whenever ε≥k. This does not give control for smaller regularizations.
-- source:
--   monocap-tech/weil, Screening/ArithmeticShift.lean; native Connes/ArithmeticRegularization.lean supplies the premise from the proved original archimedean, pole and prime bound, with the complete actual-zero negative synthesis and original physical metric. It proves the unchanged selected marker half-bound above K(R), actual finite restoration, and the exact all-positive-regularizations/unshifted-covariance boundary.
--
--   Literature/source audit addendum (2026-10-11; COR-13): Exact native software custody, independently verified from retained local Git objects: monocap-tech/weil 33c2ccf18575bed29f503a6bdc1b580f6ec957d7, WeilDefect/Screening/ArithmeticShift.lean, SHA256 fdb186c2e0f1c2d1d4b1fa9dd66ed684ae1c72ea3ed42cff3ec01a719ec17849. Public availability of these historical pins has not been checked; this addendum verifies local source bytes and preserves the original source ancestry.

import Mathlib.Analysis.InnerProductSpace.Positive

set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder
noncomputable section
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A proved quadratic lower bound yields covariance order above that shift.
There is no assertion about smaller positive regularizations. -/

theorem WeilDefect.MarkerStability.covariance_le_regularized_of_quadratic_shift (A : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (N : K →L[ℂ] H) (k ε : ℝ) (hkε : k ≤ ε)
    (hbound : ∀ x : H, -k * ‖x‖ ^ 2 ≤
      RCLike.re ⟪A x, x⟫_ℂ - ‖N.adjoint x‖ ^ 2) :
    N ∘L N.adjoint ≤ A + ε • 1 := by sorry
