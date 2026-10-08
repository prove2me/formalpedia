-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_marker_lower_iff_cost_upper
-- name    : WeilDefect.MarkerStability.marker_lower_iff_cost_upper
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T15:37:55.710477+00:00
-- url     : https://prove2.me/theorems/d42423d0-69b4-4028-b051-4a2d8f0ed53a
-- title:
--   Every positive marker threshold is exactly the corresponding selected inverse-cost bound
-- statement:
--   For complex Hilbert spaces $H,K$, a strictly positive bounded operator $A$ on $H$, a bounded synthesis $N:K\to H$ and $\beta>0$, let $S=N^*A^{-1}N$ and $\Gamma=(I+S)^{-1}$. Then $$\beta I\preceq\Gamma\quad\Longleftrightarrow\quad S\preceq(\beta^{-1}-1)I.$$ These are the original regularized-cost and marker definitions, using their canonical ring inverse. This equivalence converts approximate endpoint marker lower bounds into exact selected inverse-cost estimates without supplying an arithmetic estimate or assuming a range condition.
-- source:
--   monocap-tech/weil; WeilDefect/Screening/MarkerEndpoint.lean, extending the certified original support-limit checkpoint. Exact threshold equivalence for the original marker and selected inverse cost, used by the original actual-zero arithmetic endpoint reduction. No endpoint lower bound, critical-window localization, neutral-shell persistence or RH is assumed or asserted. Existing Green proposal remains in review.

import Definitions.Def_WeilMarker_regularized_cost
open scoped InnerProductSpace ComplexOrder
open WeilDefect.MarkerStability

theorem WeilDefect.MarkerStability.marker_lower_iff_cost_upper {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) (β : ℝ) (hβ : 0 < β) :
    β • (1 : K →L[ℂ] K) ≤ marker A N ↔
      selectedCost A N ≤ (β⁻¹ - 1) • (1 : K →L[ℂ] K) := by sorry
