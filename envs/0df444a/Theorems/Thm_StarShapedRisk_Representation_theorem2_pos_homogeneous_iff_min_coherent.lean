-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_theorem2_pos_homogeneous_iff_min_coherent
-- name    : StarShapedRisk.Representation.theorem2_pos_homogeneous_iff_min_coherent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:03:19.023992+00:00
-- url     : https://prove2.me/theorems/7b0dd9b7-0475-4a49-be23-dcfd163214aa
-- title:
--   Theorem 2 (positively homogeneous case) — positively homogeneous risk measures are minima of coherent risk measures
-- statement:
--   Let $\rho:\mathcal X\to\mathbb R$ be a risk measure on a space $\mathcal X$ of bounded positions containing the constants. The following are equivalent:
--
--   1. $\rho$ is positively homogeneous;
--   2. there is a collection $\Gamma$ of coherent risk measures such that
--   $$\rho(X)=\min_{\gamma\in\Gamma}\gamma(X),\qquad X\in\mathcal X;$$
--   3. there is a family $\{\mathcal A_\beta\}_{\beta\in B}$ of coherent acceptance sets (acceptance sets that are convex cones) such that
--   $$\rho(X)=\min\{m\in\mathbb R\mid X-m\in\mathcal A_\beta\text{ for some }\beta\in B\},\qquad X\in\mathcal X.$$
--
--   Moreover, if $\rho$ is positively homogeneous, then in (2) $\Gamma$ can be taken to be the set of all coherent risk measures $\gamma$ dominating $\rho$ ($\gamma(Y)\ge\rho(Y)$ for every $Y$), and in (3) the family can be taken to be the acceptance sets of those $\gamma$.
--
--   This is the "respectively" reading of Theorem 2: positively homogeneous risk measures, such as Value-at-Risk, are lower envelopes of coherent ones.
--
--   **Formalization Note** Both minima are `IsLeast` (attained). The family in (3) is a set of subsets of $\mathcal X$ (the index set $B$ is left implicit; it may be empty or infinite, and attainment forces it to be nonempty). A coherent acceptance set is an acceptance set that is convex and closed under multiplication by every $t>0$.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2643, Theorem 2 (the 'resp.' reading: positively homogeneous / coherent)

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_RiskMeasure
import Definitions.Def_StarShapedRisk_Representation_AcceptanceSet

namespace StarShapedRisk.Representation
theorem theorem2_pos_homogeneous_iff_min_coherent {Ω : Type*} (𝒳 : PositionSpace Ω)
    (ρ : 𝒳.carrier → ℝ) (hρ : IsRiskMeasure 𝒳 ρ) :
    List.TFAE
      [IsPositivelyHomogeneous 𝒳 ρ,
       ∃ Γ : Set (𝒳.carrier → ℝ), (∀ γ ∈ Γ, IsCoherentRiskMeasure 𝒳 γ) ∧
         ∀ X : 𝒳.carrier, IsLeast ((fun γ => γ X) '' Γ) (ρ X),
       ∃ 𝔄 : Set (Set 𝒳.carrier), (∀ 𝒜 ∈ 𝔄, IsCoherentAcceptanceSet 𝒳 𝒜) ∧
         ∀ X : 𝒳.carrier, IsLeast {m : ℝ | ∃ 𝒜 ∈ 𝔄, X - 𝒳.const m ∈ 𝒜} (ρ X)] ∧
    (IsPositivelyHomogeneous 𝒳 ρ →
      let Γ₀ : Set (𝒳.carrier → ℝ) :=
        {γ | IsCoherentRiskMeasure 𝒳 γ ∧ ∀ Y : 𝒳.carrier, ρ Y ≤ γ Y}
      let 𝔄₀ : Set (Set 𝒳.carrier) := (fun γ => acceptanceSet 𝒳 γ) '' Γ₀
      (∀ X : 𝒳.carrier, IsLeast ((fun γ => γ X) '' Γ₀) (ρ X)) ∧
      (∀ 𝒜 ∈ 𝔄₀, IsCoherentAcceptanceSet 𝒳 𝒜) ∧
      ∀ X : 𝒳.carrier, IsLeast {m : ℝ | ∃ 𝒜 ∈ 𝔄₀, X - 𝒳.const m ∈ 𝒜} (ρ X)) := by sorry
end StarShapedRisk.Representation
