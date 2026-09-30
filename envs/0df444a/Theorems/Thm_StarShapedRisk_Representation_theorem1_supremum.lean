-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_theorem1_supremum
-- name    : StarShapedRisk.Representation.theorem1_supremum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:55:36.277583+00:00
-- url     : https://prove2.me/theorems/0eaa953e-e4d7-460b-92c3-6230a3bc5645
-- title:
--   Theorem 1 (supremum) — the supremum of star-shaped risk measures is a star-shaped risk measure
-- statement:
--   Let $\{\rho_i\}_{i\in I}$ be a nonempty collection of star-shaped risk measures on a space $\mathcal X$ of bounded positions containing the constants. Then the supremum
--
--   $$\rho_\vee(X)=\sup_{i\in I}\rho_i(X),\qquad X\in\mathcal X,$$
--
--   is a star-shaped risk measure.
--
--   Together with the infimum part, this shows that star-shaped risk measures form a complete lattice under pointwise operations, and it covers robustifications such as the worst case over a set of scenarios.
--
--   **Formalization Note** The index set is assumed nonempty. The supremum is Lean's `⨆` in $\mathbb R$, which is the true supremum because the family $\{\rho_i(X)\}$ is bounded by $\sup_\omega|X(\omega)|$.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2643, Theorem 1 (supremum)

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_RiskMeasure
import Definitions.Def_StarShapedRisk_Representation_Aggregation

namespace StarShapedRisk.Representation
theorem theorem1_supremum {Ω : Type*} (𝒳 : PositionSpace Ω) {I : Type*} [Nonempty I]
    (ρ : I → 𝒳.carrier → ℝ) (hρ : ∀ i, IsStarShapedRiskMeasure 𝒳 (ρ i)) :
    IsStarShapedRiskMeasure 𝒳 (riskSup 𝒳 ρ) := by sorry
end StarShapedRisk.Representation
