-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_nbhdPt_comp_appLE
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.nbhdPt_comp_appLE
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:32:52.338246+00:00
-- url     : https://prove2.me/theorems/e760a434-6bdf-56cb-9c6b-98ee9583a267
-- title:
--   Pullback Sections: nbhd Pt comp app LE
-- statement:
--   The Pullback Sections construction uses the nbhd Pt comp app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetA.lean#L143-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetA.lean#L143-L153

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
variable {Y : Scheme.{0}}
variable (y₀ : Y) (A : CommRingCat.{0})
variable {y₀ A}
set_option backward.isDefEq.respectTransparency false

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.nbhdPt_comp_appLE [IsLocalRing A] {Y' : Scheme.{0}} (φ : Y ⟶ Y')
    (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU)
    (hloc : ∀ (U : Y.Opens) (hU : y₀ ∈ U) (f : Γ(Y, U)), IsUnit (ψ U hU f) → y₀ ∈ Y.basicOpen f)
    (U' : Y'.Opens) (hU' : φ y₀ ∈ U') (h : ⊤ ≤ (nbhdPt ψ hψ ≫ φ) ⁻¹ᵁ U') :
    (nbhdPt ψ hψ ≫ φ).appLE U' ⊤ h = φ.app U' ≫ ψ (φ ⁻¹ᵁ U') hU' ≫ (Scheme.ΓSpecIso A).inv := by sorry
