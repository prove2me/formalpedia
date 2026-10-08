-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_negative_margin_forbids_marker_lower
-- name    : WeilDefect.MarkerStability.negative_margin_forbids_marker_lower
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T07:06:07.349187+00:00
-- url     : https://prove2.me/theorems/072d9df5-5c0b-4fcd-ac34-67d63ea08953
-- title:
--   A quantitative physical gap excludes a scalar marker lower bound
-- statement:
--   For original bounded syntheses $P,N$ between complete complex Hilbert spaces, if $\kappa>0$, $\varepsilon>0$ and $\kappa(\|P^*x\|^2+\varepsilon\|x\|^2)<\|N^*x\|^2$, then the original marker $\Gamma(PP^*+\varepsilon I,N)$ fails the lower bound $(\kappa+1)^{-1}I$. This retains the original covariance and metric. The native actual-zero quartet corollary chooses $\kappa>1$ uniformly before selecting any larger support window or sufficiently small regularization.
-- source:
--   monocap-tech/weil native base b019d40205680f9761a4b0a80cbcad56ee1b606b; exact new sources Screening/MarkerMargin.lean and Connes/CanonicalGreenMarkerMargin.lean in Connes_Weil_Uniform_Marker_Margin.zip. Explicit reductions, not unconditional arithmetic marker positivity or RH.

import Definitions.Def_WeilMarker_regularized_cost
open scoped InnerProductSpace ComplexOrder Topology
open Filter WeilDefect.MarkerStability

theorem WeilDefect.MarkerStability.negative_margin_forbids_marker_lower {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (P : K →L[ℂ] H)
    {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (N : J →L[ℂ] H) (x : H) (κ ε : ℝ) (hκ : 0 < κ) (hε : 0 < ε)
    (hgap : κ * (‖P.adjoint x‖ ^ 2 + ε * ‖x‖ ^ 2) < ‖N.adjoint x‖ ^ 2) :
    ¬ (κ + 1)⁻¹ • (1 : J →L[ℂ] J) ≤ marker (P ∘L P.adjoint + ε • 1) N := by sorry
