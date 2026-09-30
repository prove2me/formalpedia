-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_theorem1_average
-- name    : StarShapedRisk.Representation.theorem1_average
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:58:48.299245+00:00
-- url     : https://prove2.me/theorems/54f3f99b-58ac-4505-99ba-b16d7b6708eb
-- title:
--   Theorem 1 (average) — the $\mu$-average of star-shaped risk measures is a star-shaped risk measure
-- statement:
--   Let $\{\rho_i\}_{i\in I}$ be a collection of star-shaped risk measures on a space $\mathcal X$ of bounded positions containing the constants, and let $\mu$ be a probability measure on the set of all subsets of $I$. Then the average
--
--   $$\rho_\mu(X)=\int_I\rho_i(X)\,d\mu(i),\qquad X\in\mathcal X,$$
--
--   is a star-shaped risk measure. In particular, every convex combination $\sum_i c_i\rho_i$ of finitely many star-shaped risk measures is one.
--
--   Averaging risk assessments across models or experts therefore preserves star-shapedness.
--
--   **Formalization Note** The σ-algebra on $I$ is the power set (hypothesis `‹MeasurableSpace I› = ⊤`) and $\mu$ is a countably additive probability measure; the integral is Lean's Bochner integral. Every map $i\mapsto\rho_i(X)$ is then measurable and bounded (by $\sup_\omega|X(\omega)|$), hence integrable, so the integral is never the junk value of a non-integrable function.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2643, Theorem 1 (average, Eq. (8))

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_RiskMeasure
import Definitions.Def_StarShapedRisk_Representation_Aggregation

namespace StarShapedRisk.Representation
theorem theorem1_average {Ω : Type*} (𝒳 : PositionSpace Ω) {I : Type*} [MeasurableSpace I]
    (hI : ‹MeasurableSpace I› = ⊤) (μ : MeasureTheory.Measure I)
    [MeasureTheory.IsProbabilityMeasure μ]
    (ρ : I → 𝒳.carrier → ℝ) (hρ : ∀ i, IsStarShapedRiskMeasure 𝒳 (ρ i)) :
    IsStarShapedRiskMeasure 𝒳 (riskAverage 𝒳 μ ρ) := by sorry
end StarShapedRisk.Representation
