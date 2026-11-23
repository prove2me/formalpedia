-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_hom_ext_of_local
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.hom_ext_of_local
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:20.585463+00:00
-- url     : https://prove2.me/theorems/ef4b61e7-e5ba-43b8-9f22-7991558f45bf
-- title:
--   Pullback Sections: hom ext of local
-- statement:
--   The Pullback Sections construction uses the hom ext of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetA.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetA.lean#L25-L36

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
set_option backward.isDefEq.respectTransparency false

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.hom_ext_of_local {R : CommRingCat.{0}} [IsLocalRing R] {f₁ f₂ : Spec R ⟶ Y}
    (hpt : f₁ (IsLocalRing.closedPoint R) = f₂ (IsLocalRing.closedPoint R))
    (happ : ∀ (U : Y.Opens) (h₁ : ⊤ ≤ f₁ ⁻¹ᵁ U) (h₂ : ⊤ ≤ f₂ ⁻¹ᵁ U), f₁.appLE U ⊤ h₁ = f₂.appLE U ⊤ h₂) :
    f₁ = f₂ := by sorry
