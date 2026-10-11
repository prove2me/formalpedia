-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_nonnegative_compression_kernel_iff
-- name    : WeilDefect.MarkerStability.nonnegative_compression_kernel_iff
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T18:46:45.324406+00:00
-- url     : https://prove2.me/theorems/f411adfa-5be4-45fa-aff9-08606b6ad0c8
-- title:
--   Positive covariance compression preserves attained neutral kernels
-- statement:
--   Let $H,K$ be complete complex Hilbert spaces, $A:K\to K$ a bounded positive operator, and $U:H\to K$ any bounded linear map. For every $x\in H$, $$U^*AUx=0\quad\Longleftrightarrow\quad AUx=0.$$ Positivity is required on the larger operator $A$, not only on its compression. No inverse, closed-range or finite-dimensional premise is used. The original Green specialization proves conditional persistence of attained physical neutral directions; it does not establish the arithmetic half-bound or general neutral-shell persistence.
-- source:
--   monocap-tech/weil, Screening/NeutralCompression.lean and Connes/CanonicalGreenNeutralShell.lean. The native specialization retains the original support isometry, physical metrics, selected packet, all actual positive zero actors and analytic multiplicities. The unconditional companion theorem isolates the missing orthogonal-shell leakage term.
--
--   Literature/source audit addendum (2026-10-11; COR-15): Exact native software custody, independently verified from retained local Git objects: monocap-tech/weil 9a89f62df672f194fe442e1d36bf79fdc3486ec4, WeilDefect/Screening/NeutralCompression.lean, SHA256 1eca8e3a9396e93e8d61f7f8927dfd1b7817ce2d03d2692d3d704ef2c9c05c79. Public availability of these historical pins has not been checked; this addendum verifies local source bytes and preserves the original source ancestry.

import Definitions.Def_WeilMarker_regularized_cost
set_option autoImplicit false
open scoped InnerProductSpace ComplexOrder
noncomputable section
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem WeilDefect.MarkerStability.nonnegative_compression_kernel_iff (A : K →L[ℂ] K) (hA : 0 ≤ A)
    (U : H →L[ℂ] K) (x : H) :
    (U.adjoint ∘L A ∘L U) x = 0 ↔ A (U x) = 0 := by sorry
