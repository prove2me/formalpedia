-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_regularized_marker_isometric_compression
-- name    : WeilDefect.MarkerStability.regularized_marker_isometric_compression
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T14:03:19.374177+00:00
-- url     : https://prove2.me/theorems/af00fe85-6893-4ac6-baf2-1329aa2f4bfe
-- title:
--   Original regularized markers decrease under isometric carrier enlargement
-- statement:
--   Let $H,K,J,Q$ be complete complex Hilbert spaces, $U:H\to K$ a linear isometry, and $P:Q\to K$, $N:J\to K$ bounded original syntheses. For $\varepsilon>0$, let $p=U^*P$ and $n=U^*N$. Then the original selected marker obeys
--   $$\Gamma(PP^*+\varepsilon I,N)\preceq\Gamma(pp^*+\varepsilon I,n),\qquad\Gamma(A,N)=(I+N^*A^{-1}N)^{-1}.$$
--   The source metrics and coefficient carrier are unchanged. This is the operator bridge for comparing the original Green actors on nested physical support windows; no range inclusion, inverse-cost bound or arithmetic positivity premise is needed.
-- source:
--   monocap-tech/weil native base b019d40205680f9761a4b0a80cbcad56ee1b606b; exact new source modules Connes/CanonicalGreenWindowInclusion.lean, Screening/MarkerCompression.lean and Connes/CanonicalGreenSupportLimit.lean in Connes_Weil_Original_Support_Limit.zip. Both ordered norm limits are proved natively; prescribed critical endpoint identification, support containment, arithmetic lower bounds and RH are not assumed or asserted.

import Definitions.Def_WeilMarker_regularized_cost
open scoped InnerProductSpace ComplexOrder Topology
open ContinuousLinearMap WeilDefect.MarkerStability

theorem WeilDefect.MarkerStability.regularized_marker_isometric_compression {H K J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (U : H →ₗᵢ[ℂ] K) (P : Q →L[ℂ] K) (N : J →L[ℂ] K)
    (ε : ℝ) (hε : 0 < ε) :
    marker (P ∘L P.adjoint + ε • 1) N ≤
      marker ((U.toContinuousLinearMap.adjoint ∘L P) ∘L
        (U.toContinuousLinearMap.adjoint ∘L P).adjoint + ε • 1)
        (U.toContinuousLinearMap.adjoint ∘L N) := by sorry
