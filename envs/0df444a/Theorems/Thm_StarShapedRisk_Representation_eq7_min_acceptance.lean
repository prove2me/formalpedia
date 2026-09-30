-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_eq7_min_acceptance
-- name    : StarShapedRisk.Representation.eq7_min_acceptance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:50:04.70499+00:00
-- url     : https://prove2.me/theorems/19bd1e8a-1d3d-441f-9750-925c1487b376
-- title:
--   Eq. (7) — a risk measure is the minimal capital making a position acceptable
-- statement:
--   Let $\rho:\mathcal X\to\mathbb R$ be a risk measure on a space $\mathcal X$ of bounded positions containing the constants, and $\mathcal A_\rho=\{X\mid\rho(X)\le0\}$ its acceptance set. Then for every $X\in\mathcal X$ the minimum below is attained and
--
--   $$\rho(X)=\min\{m\in\mathbb R\mid X-m\in\mathcal A_\rho\}.$$
--
--   In words, the risk of $X$ is the least amount by which the loss must be uniformly reduced to make the position acceptable; in particular $\mathcal A_\rho$ determines $\rho$.
--
--   **Formalization Note** "min" is stated as `IsLeast`: $\rho(X)$ belongs to the set and is a lower bound of it.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2642, Eq. (7)

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_RiskMeasure
import Definitions.Def_StarShapedRisk_Representation_AcceptanceSet

namespace StarShapedRisk.Representation
theorem eq7_min_acceptance {Ω : Type*} (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ)
    (hρ : IsRiskMeasure 𝒳 ρ) (X : 𝒳.carrier) :
    IsLeast {m : ℝ | X - 𝒳.const m ∈ acceptanceSet 𝒳 ρ} (ρ X) := by sorry
end StarShapedRisk.Representation
