-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_proposition3_subadditive_star_shaped_iff
-- name    : StarShapedRisk.Representation.proposition3_subadditive_star_shaped_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:02:28.114987+00:00
-- url     : https://prove2.me/theorems/35648575-6006-4490-b39d-e7addb4b4f03
-- title:
--   Proposition 3 — for subadditive risk measures, star-shaped ⇔ positively homogeneous ⇔ convex
-- statement:
--   Let $\rho:\mathcal X\to\mathbb R$ be a subadditive risk measure on a space $\mathcal X$ of bounded positions containing the constants: $\rho(X+Y)\le\rho(X)+\rho(Y)$ for all $X,Y$. The following are equivalent:
--
--   1. $\rho$ is star-shaped;
--   2. $\rho$ is positively homogeneous (thus coherent);
--   3. $\rho$ is convex.
--
--   Hence coherent risk measures are exactly the subadditive star-shaped ones, and positive homogeneity in the definition of coherence can be weakened to star-shapedness.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2642, Proposition 3

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_RiskMeasure

namespace StarShapedRisk.Representation
theorem proposition3_subadditive_star_shaped_iff {Ω : Type*} (𝒳 : PositionSpace Ω)
    (ρ : 𝒳.carrier → ℝ) (hρ : IsRiskMeasure 𝒳 ρ) (hsub : IsSubadditive 𝒳 ρ) :
    List.TFAE [IsStarShaped 𝒳 ρ, IsPositivelyHomogeneous 𝒳 ρ, IsConvex 𝒳 ρ] := by sorry
end StarShapedRisk.Representation
