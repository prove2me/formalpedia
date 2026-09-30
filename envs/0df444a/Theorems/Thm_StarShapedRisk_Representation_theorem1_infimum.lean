-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_theorem1_infimum
-- name    : StarShapedRisk.Representation.theorem1_infimum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:52:51.396957+00:00
-- url     : https://prove2.me/theorems/3a5e4d26-0ab8-498a-910d-3691237b15ae
-- title:
--   Theorem 1 (infimum) — the infimum of star-shaped risk measures is a star-shaped risk measure
-- statement:
--   Let $\{\rho_i\}_{i\in I}$ be a nonempty collection of star-shaped risk measures on a space $\mathcal X$ of bounded positions containing the constants. Then the infimum
--
--   $$\rho_\wedge(X)=\inf_{i\in I}\rho_i(X),\qquad X\in\mathcal X,$$
--
--   is a star-shaped risk measure.
--
--   This is the part of Theorem 1 that shows a minimum of convex risk measures is star-shaped, one direction of the representation theorem.
--
--   **Formalization Note** The index set is assumed nonempty (an empty collection has no real infimum). The infimum is Lean's `⨅` in $\mathbb R$; since $\inf_\omega X(\omega)\le\rho_i(X)\le\sup_\omega X(\omega)$ for every risk measure, the family is bounded and the value is the true infimum.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2643, Theorem 1 (infimum)

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_RiskMeasure
import Definitions.Def_StarShapedRisk_Representation_Aggregation

namespace StarShapedRisk.Representation
theorem theorem1_infimum {Ω : Type*} (𝒳 : PositionSpace Ω) {I : Type*} [Nonempty I]
    (ρ : I → 𝒳.carrier → ℝ) (hρ : ∀ i, IsStarShapedRiskMeasure 𝒳 (ρ i)) :
    IsStarShapedRiskMeasure 𝒳 (riskInf 𝒳 ρ) := by sorry
end StarShapedRisk.Representation
