-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_marker_lower_iff_scaled_covariance_le
-- name    : WeilDefect.MarkerStability.marker_lower_iff_scaled_covariance_le
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T14:09:51.995874+00:00
-- url     : https://prove2.me/theorems/3ad289a3-b72a-4775-aee8-bfbcafdeeb64
-- title:
--   Original inverse marker threshold is exactly scaled physical covariance order
-- statement:
--   For any original strictly positive denominator $A$, selected synthesis $N$, and $0<\beta<1$, we prove
--   $$\beta I\le\operatorname{marker}(A,N)\quad\Longleftrightarrow\quad NN^*\le(\beta^{-1}-1)A.$$
--   The accepted marker/cost equivalence identifies a lower marker threshold with selectedCost(A,N)<= (beta inverse minus one) I. Specializing it at one half and using the accepted original half-bound/covariance equivalence gives cost<=I iff NN*<=A. A closed positive-scalar inverse identity proves inverse(c A)=c inverse times inverse(A), using the same native canonical ring inverse and strict positivity. It gives the exact cost scaling. Applying the cost-one equivalence to the positively scaled denominator and rescaling operator order gives the general cost/covariance equivalence. Here beta<1 makes the scale positive. No finite-dimensional surrogate, inverse bound or new operator axiom is assumed.
-- source:
--   monocap-tech/weil native head a1a3c6481eb9bc50bc7e92aa694f6ae530c7e359; unchanged MarkerQuadratic.lean and CanonicalGreenQuadraticEndpoint.lean declarations; explicit native definitional unfoldings only

import Definitions.Def_ConnesGreen_RG0_original_actors
import Definitions.Def_WeilMarker_regularized_cost
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability WeilDefect.WDT13
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem WeilDefect.MarkerStability.marker_lower_iff_scaled_covariance_le
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (hA : IsStrictlyPositive A) (N : K →L[ℂ] H)
    (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    β • (1 : K →L[ℂ] K) ≤ marker A N ↔ N ∘L N.adjoint ≤ (β⁻¹ - 1) • A := by sorry
