-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_Supplement_theorem3_average
-- name    : StarShapedRisk.Representation.Supplement.theorem3_average
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:40:26.43786+00:00
-- url     : https://prove2.me/theorems/3c7646df-d249-42bd-b69e-9776580e34ae
-- title:
--   Theorem 3 (average) — attained minimum of selection averages
-- statement:
--   Let $\rho_i$ be star-shaped risk measures on a linear space $\mathcal X$ of bounded losses. Let $\Gamma_i$ consist of convex risk measures satisfying $\rho_i(X)=\min_{\gamma\in\Gamma_i}\gamma(X)$ for every $i,X$. For a probability $\mu$ defined on all subsets of the index set,
--   $$\int_I\rho_i(X)\,d\mu(i)=\min_{\delta\in\int\Gamma_i\,d\mu(i)}\delta(X)\qquad(X\in\mathcal X).$$
--   Here the family on the right includes every average of a selection $\gamma_i\in\Gamma_i$. In particular, the minimum is attained at each position. This describes how convex envelopes behave under averaging.
--
--   Differences from the source:
--   - encoding: min and inf in (13)–(16) → IsLeast for attained minima and IsGLB for infima; reason: retain attainment and exclude default values of real extrema
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), DOI 10.1287/opre.2022.2303, p. 2644, Theorem 3 (average)

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_Supplement_SelectionEnvelopes

namespace StarShapedRisk.Representation.Supplement

theorem theorem3_average {Ω : Type*} (𝒳 : PositionSpace Ω) {I : Type*}
    [MeasurableSpace I] (hI : ‹MeasurableSpace I› = ⊤)
    (μ : MeasureTheory.Measure I) [MeasureTheory.IsProbabilityMeasure μ]
    (ρ : I → 𝒳.carrier → ℝ) (Γ : I → Set (𝒳.carrier → ℝ))
    (hρ : ∀ i, IsStarShapedRiskMeasure 𝒳 (ρ i))
    (hΓ : ∀ i, ∀ γ ∈ Γ i, IsConvexRiskMeasure 𝒳 γ)
    (hmin : ∀ i X, IsLeast {r : ℝ | ∃ γ ∈ Γ i, r = γ X} (ρ i X)) :
    ∀ X, IsLeast {r : ℝ | ∃ δ ∈ averageSelections 𝒳 μ Γ, r = δ X}
      (riskAverage 𝒳 μ ρ X) := by sorry

end StarShapedRisk.Representation.Supplement
