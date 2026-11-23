-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_nbhdPt_appLE
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.nbhdPt_appLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:03.597168+00:00
-- url     : https://prove2.me/theorems/4bf0a39e-001d-4662-a701-4375072a1c76
-- title:
--   Pullback Sections: nbhd Pt app LE
-- statement:
--   The Pullback Sections construction uses the nbhd Pt app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetA.lean#L99-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetA.lean#L99-L114

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.nbhdPt_appLE [IsLocalRing A] (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU)
    (hloc : ∀ (U : Y.Opens) (hU : y₀ ∈ U) (f : Γ(Y, U)), IsUnit (ψ U hU f) → y₀ ∈ Y.basicOpen f)
    (U : Y.Opens) (hU : y₀ ∈ U) (h : ⊤ ≤ nbhdPt ψ hψ ⁻¹ᵁ U) :
    (nbhdPt ψ hψ).appLE U ⊤ h = ψ U hU ≫ (Scheme.ΓSpecIso A).inv := by sorry
