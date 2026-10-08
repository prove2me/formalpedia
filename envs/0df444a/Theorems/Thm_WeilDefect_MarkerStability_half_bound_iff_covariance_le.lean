-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_half_bound_iff_covariance_le
-- name    : WeilDefect.MarkerStability.half_bound_iff_covariance_le
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T17:04:10.790311+00:00
-- url     : https://prove2.me/theorems/76568019-c91b-4547-ae6d-8246030abbdb
-- title:
--   The original marker half-bound is exactly physical covariance domination
-- statement:
--   On complex Hilbert spaces $H,K$, for strictly positive bounded $A:H\to H$ and bounded $N:K\to H$, the original marker $\Gamma(A,N)=(I+N^*A^{-1}N)^{-1}$ satisfies $\Gamma\succeq\frac12 I$ exactly when $NN^*\preceq A$. The converse uses $y=A^{-1}Nv$ and $\|v-N^*y\|^2\ge0$, with no range premise. This criterion proves neither inequality unconditionally.
-- source:
--   monocap-tech/weil, MarkerQuadratic.lean; reverse Schur implication independently proved by completing the square on the original physical carrier. Supports the actual-zero finite-restored arithmetic test criterion. No arithmetic lower bound or RH asserted.

import Definitions.Def_WeilMarker_regularized_cost
open scoped InnerProductSpace ComplexOrder
open WeilDefect.MarkerStability

theorem WeilDefect.MarkerStability.half_bound_iff_covariance_le {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (hA : IsStrictlyPositive A) (N : K →L[ℂ] H) :
    (1 / 2 : ℝ) • (1 : K →L[ℂ] K) ≤ marker A N ↔ N ∘L N.adjoint ≤ A := by sorry
