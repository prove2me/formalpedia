-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_theorem1_inf_convolution
-- name    : StarShapedRisk.Representation.theorem1_inf_convolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:00:49.675371+00:00
-- url     : https://prove2.me/theorems/abb4d9c9-56a7-4ded-8979-b020717d6059
-- title:
--   Theorem 1 (inf-convolution) — the inf-convolution of star-shaped risk measures is a star-shaped risk measure
-- statement:
--   Let $n\ge1$ and let $\rho_1,\dots,\rho_n$ be star-shaped risk measures on a space $\mathcal X$ of bounded positions containing the constants, satisfying the normality condition
--
--   $$\sum_{i=1}^n\rho_i(Z_i)\ge0\quad\text{for all }Z_1,\dots,Z_n\in\mathcal X\text{ with }\sum_{i=1}^n Z_i=0.\qquad(10)$$
--
--   Then the inf-convolution
--
--   $$\rho_\diamond(X)=\inf\Big\{\sum_{i=1}^n\rho_i(Y_i)\ \Big|\ Y_1,\dots,Y_n\in\mathcal X,\ \sum_{i=1}^nY_i=X\Big\}$$
--
--   is a star-shaped risk measure (in particular, real valued).
--
--   The inf-convolution describes optimal risk sharing among $n$ agents, so the result says that star-shapedness survives risk sharing.
--
--   **Formalization Note** The index set is `Fin n` with $0<n$, and (10) is an explicit hypothesis. The infimum is Lean's real `sInf`; under (10) the set is nonempty and bounded below, so its value is the genuine infimum.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2643, Theorem 1 (inf-convolution, Eqs. (9)-(10))

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_RiskMeasure
import Definitions.Def_StarShapedRisk_Representation_Aggregation

namespace StarShapedRisk.Representation
theorem theorem1_inf_convolution {Ω : Type*} (𝒳 : PositionSpace Ω) {n : ℕ} (hn : 0 < n)
    (ρ : Fin n → 𝒳.carrier → ℝ) (hρ : ∀ i, IsStarShapedRiskMeasure 𝒳 (ρ i))
    (h10 : NormalityCondition 𝒳 ρ) :
    IsStarShapedRiskMeasure 𝒳 (infConvolution 𝒳 ρ) := by sorry
end StarShapedRisk.Representation
