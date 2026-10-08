-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_tail_marker_stability
-- name    : WeilDefect.MarkerStability.tail_marker_stability
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T05:25:36.679459+00:00
-- url     : https://prove2.me/theorems/d6363973-128c-46da-8a27-a284f20e4224
-- title:
--   Inverse-stable marker bound at the linear tail-to-regularization scale
-- statement:
--   Let $H,K$ be complete complex Hilbert spaces, $L,R:H\to H$ bounded nonnegative operators, and $N:K\to H$ any bounded selected synthesis. If $\varepsilon>0$, $0\le\alpha<1$ and $\|R\|\le\alpha\varepsilon$, put $A=L+\varepsilon I$ and $B=A-R$. Then $B$ is strictly positive, so both physical inverses exist, and
--   $$0\le\Gamma(A,N)-\Gamma(B,N),\qquad \|\Gamma(A,N)-\Gamma(B,N)\|\le\alpha,$$
--   where $\Gamma(A,N)=(I+N^*A^{-1}N)^{-1}$. No bound on the selected inverse cost or on $\|N\|$ is a hypothesis. The factor uses the ratio of tail size to $\varepsilon$, rather than to $\varepsilon^2$.
--
--   This is a conservative marker recovery estimate for finite negative-background restoration. It is not the sharper scalar-optimal constant stated in the arithmetic notes, and it proves no half-threshold bound or endpoint-limit interchange. Instantiation on the original actual-zero Green carrier is supplied by a separate theorem.
-- source:
--   monocap-tech/weil, WeilDefect/Screening/ShortedCovariance.lean (operatorInverse), WeilDefect/Screening/MarkerStability.lean (selectedCost, marker), and provenance/rh/checkpoints/RH_ZERO_PROV_4_INFINITE_NBR_DIAGONAL_MARKER_STABILITY_20260920.md, equations (3)-(8). Native base commit b019d40205680f9761a4b0a80cbcad56ee1b606b; exact new source is in Connes_Weil_Green_Marker_Recovery.zip.

import Definitions.Def_WeilMarker_regularized_cost
open scoped InnerProduct ComplexOrder
open WeilDefect.MarkerStability

theorem WeilDefect.MarkerStability.tail_marker_stability {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (L R : H →L[ℂ] H) (N : K →L[ℂ] H)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (ε α : ℝ)
    (hε : 0 < ε) (hα : 0 ≤ α) (hα1 : α < 1) (htail : ‖R‖ ≤ α * ε) :
    IsStrictlyPositive (L + ε • (1 : H →L[ℂ] H) - R) ∧
      0 ≤ marker (L + ε • (1 : H →L[ℂ] H)) N -
        marker (L + ε • (1 : H →L[ℂ] H) - R) N ∧
      ‖marker (L + ε • (1 : H →L[ℂ] H)) N -
        marker (L + ε • (1 : H →L[ℂ] H) - R) N‖ ≤ α := by sorry
