-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_proposition2_star_shaped_iff_acceptance
-- name    : StarShapedRisk.Representation.proposition2_star_shaped_iff_acceptance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:51:43.939984+00:00
-- url     : https://prove2.me/theorems/69c9e96e-07ac-4b74-970c-4b01d883906d
-- title:
--   Proposition 2 — $\rho$ is star-shaped iff its acceptance set is star-shaped
-- statement:
--   Let $\rho:\mathcal X\to\mathbb R$ be a risk measure on a space $\mathcal X$ of bounded positions containing the constants. Recall that a subset $S$ of a vector space is star-shaped if $\lambda s\in S$ for all $\lambda\in[0,1]$ and all $s\in S$. The following are equivalent:
--
--   1. $\rho$ is star-shaped;
--   2. the acceptance set $\mathcal A_\rho=\{X\mid\rho(X)\le0\}$ is star-shaped in $\mathcal X$;
--   3. there exists a star-shaped acceptance set $\mathcal A$ with $\rho=\rho_{\mathcal A}$, where $\rho_{\mathcal A}(X)=\inf\{m\mid X-m\in\mathcal A\}$.
--
--   This is the principle behind star-shapedness: deleveraging an acceptable position keeps it acceptable.
--
--   **Formalization Note** Star-shaped sets are Mathlib's `StarConvex ℝ 0`, which is exactly the page's definition. Acceptance sets carry both axioms (least upper bound $0$ of the constants, downward closedness).
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2642, Proposition 2

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_RiskMeasure
import Definitions.Def_StarShapedRisk_Representation_AcceptanceSet

namespace StarShapedRisk.Representation
theorem proposition2_star_shaped_iff_acceptance {Ω : Type*} (𝒳 : PositionSpace Ω)
    (ρ : 𝒳.carrier → ℝ) (hρ : IsRiskMeasure 𝒳 ρ) :
    List.TFAE
      [IsStarShaped 𝒳 ρ,
       StarConvex ℝ (0 : 𝒳.carrier) (acceptanceSet 𝒳 ρ),
       ∃ 𝒜 : Set 𝒳.carrier, IsAcceptanceSet 𝒳 𝒜 ∧ StarConvex ℝ (0 : 𝒳.carrier) 𝒜 ∧
         ρ = riskOf 𝒳 𝒜] := by sorry
end StarShapedRisk.Representation
