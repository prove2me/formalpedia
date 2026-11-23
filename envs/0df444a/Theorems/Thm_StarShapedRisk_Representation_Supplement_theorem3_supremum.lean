-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_Supplement_theorem3_supremum
-- name    : StarShapedRisk.Representation.Supplement.theorem3_supremum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:41:05.722728+00:00
-- url     : https://prove2.me/theorems/4a52349b-9490-4793-84a2-20a176bd13b5
-- title:
--   Theorem 3 (supremum) — intersection of relaxed convex envelopes
-- statement:
--   Let $I$ be nonempty and let $\rho_i=\min_{\gamma\in\Gamma_i}\gamma$ be star-shaped risk measures with each $\Gamma_i$ a set of convex risk measures and every displayed minimum attained. Then
--   $$\sup_{i\in I}\rho_i(X)=\min_{\delta\in\bigcap_i\widetilde\Gamma_i}\delta(X)\qquad(X\in\mathcal X).$$
--   The relaxation permits a different member of $\Gamma_i$ below $\delta$ at each position. The intersection is of these relaxations, and the minimum over it is attained. This gives the envelope of a supremum without requiring the original families to intersect.
--
--   Differences from the source:
--   - encoding: min and inf in (13)–(16) → IsLeast for attained minima and IsGLB for infima; reason: retain attainment and exclude default values of real extrema
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), DOI 10.1287/opre.2022.2303, p. 2644, Theorem 3 (supremum)

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_Supplement_SelectionEnvelopes

namespace StarShapedRisk.Representation.Supplement

theorem theorem3_supremum {Ω : Type*} (𝒳 : PositionSpace Ω) {I : Type*} [Nonempty I]
    (ρ : I → 𝒳.carrier → ℝ) (Γ : I → Set (𝒳.carrier → ℝ))
    (hρ : ∀ i, IsStarShapedRiskMeasure 𝒳 (ρ i))
    (hΓ : ∀ i, ∀ γ ∈ Γ i, IsConvexRiskMeasure 𝒳 γ)
    (hmin : ∀ i X, IsLeast {r : ℝ | ∃ γ ∈ Γ i, r = γ X} (ρ i X)) :
    ∀ X, IsLeast {r : ℝ | ∃ δ : 𝒳.carrier → ℝ,
      (∀ i, δ ∈ relaxation 𝒳 (Γ i)) ∧ r = δ X} (riskSup 𝒳 ρ X) := by sorry

end StarShapedRisk.Representation.Supplement
