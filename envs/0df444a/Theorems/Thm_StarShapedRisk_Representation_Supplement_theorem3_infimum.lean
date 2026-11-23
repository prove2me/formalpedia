-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_Supplement_theorem3_infimum
-- name    : StarShapedRisk.Representation.Supplement.theorem3_infimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:43:12.922208+00:00
-- url     : https://prove2.me/theorems/776b9d6c-d00d-442f-9e1f-c5562f2c236a
-- title:
--   Theorem 3 (infimum) — union of envelopes and conditional attainment
-- statement:
--   Let $I$ be nonempty, $\rho_i$ star-shaped risk measures, and $\Gamma_i$ sets of convex risk measures with $\rho_i(X)=\min_{\gamma\in\Gamma_i}\gamma(X)$ for every position. Then
--   $$\inf_{i\in I}\rho_i(X)=\inf_{\gamma\in\bigcup_i\Gamma_i}\gamma(X).$$
--   If the left infimum is attained by some $i\in I$, the right infimum is also attained. Both assertions hold at every $X\in\mathcal X$. This distinguishes a general infimum envelope from an attained one.
--
--   Differences from the source:
--   - encoding: min and inf in (13)–(16) → IsLeast for attained minima and IsGLB for infima; reason: retain attainment and exclude default values of real extrema
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), DOI 10.1287/opre.2022.2303, p. 2644, Theorem 3 (infimum)

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_Supplement_SelectionEnvelopes

namespace StarShapedRisk.Representation.Supplement

theorem theorem3_infimum {Ω : Type*} (𝒳 : PositionSpace Ω) {I : Type*} [Nonempty I]
    (ρ : I → 𝒳.carrier → ℝ) (Γ : I → Set (𝒳.carrier → ℝ))
    (hρ : ∀ i, IsStarShapedRiskMeasure 𝒳 (ρ i))
    (hΓ : ∀ i, ∀ γ ∈ Γ i, IsConvexRiskMeasure 𝒳 γ)
    (hmin : ∀ i X, IsLeast {r : ℝ | ∃ γ ∈ Γ i, r = γ X} (ρ i X)) :
    ∀ X, IsGLB {r : ℝ | ∃ i, ∃ γ ∈ Γ i, r = γ X} (riskInf 𝒳 ρ X) ∧
      ((∃ i, ρ i X = riskInf 𝒳 ρ X) →
        IsLeast {r : ℝ | ∃ i, ∃ γ ∈ Γ i, r = γ X} (riskInf 𝒳 ρ X)) := by sorry

end StarShapedRisk.Representation.Supplement
