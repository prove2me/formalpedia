-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_lower_bound_excluded_by_uniform_gap
-- name    : WeilDefect.MarkerStability.lower_bound_excluded_by_uniform_gap
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T07:07:09.792449+00:00
-- url     : https://prove2.me/theorems/7d586c22-fdfb-40ab-8d24-de93a927f2b3
-- title:
--   A uniform scalar marker gap survives norm limits
-- statement:
--   Let $G_i$ be eventually self-adjoint bounded operators on one fixed complete complex Hilbert space, indexed by a nontrivial filter. Suppose eventually $G_i\not\succeq\beta I$, $\beta<\theta$, and $G_i$ converges in norm to $G_0$. Then $G_0\not\succeq\theta I$. Norm convergence, a common strict gap and fixed coefficient-carrier custody are explicit premises. Applying this twice gives the native ordered regularization-then-support limit obstruction without interchanging limits.
-- source:
--   monocap-tech/weil native base b019d40205680f9761a4b0a80cbcad56ee1b606b; exact new sources Screening/MarkerMargin.lean and Connes/CanonicalGreenMarkerMargin.lean in Connes_Weil_Uniform_Marker_Margin.zip. Explicit reductions, not unconditional arithmetic marker positivity or RH.

import Definitions.Def_WeilMarker_regularized_cost
open scoped InnerProductSpace ComplexOrder Topology
open Filter WeilDefect.MarkerStability

theorem WeilDefect.MarkerStability.lower_bound_excluded_by_uniform_gap {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (G : ι → K →L[ℂ] K) (G₀ : K →L[ℂ] K) (β θ : ℝ) (hβ : β < θ)
    (hself : ∀ᶠ i in l, IsSelfAdjoint (G i))
    (hgap : ∀ᶠ i in l, ¬ β • (1 : K →L[ℂ] K) ≤ G i)
    (hlim : Tendsto G l (nhds G₀)) :
    ¬ θ • (1 : K →L[ℂ] K) ≤ G₀ := by sorry
