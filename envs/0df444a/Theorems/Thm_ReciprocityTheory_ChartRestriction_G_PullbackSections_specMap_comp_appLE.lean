-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_specMap_comp_appLE
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.specMap_comp_appLE
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:44:43.95384+00:00
-- url     : https://prove2.me/theorems/a75e5009-ef4c-4f23-acaa-563cf2373af8
-- title:
--   Pullback Sections: spec Map comp app LE
-- statement:
--   The Pullback Sections construction uses the spec Map comp app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetF.lean#L16-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetF.lean#L16-L34

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
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
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {Y : Scheme.{0}}
set_option backward.isDefEq.respectTransparency false

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.specMap_comp_appLE {A B : CommRingCat.{0}} (χ : A ⟶ B) (q : Spec A ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (Spec.map χ ≫ q) ⁻¹ᵁ U) (hq : ⊤ ≤ q ⁻¹ᵁ U) :
    (Spec.map χ ≫ q).appLE U ⊤ h ≫ (Scheme.ΓSpecIso B).hom =
      q.appLE U ⊤ hq ≫ (Scheme.ΓSpecIso A).hom ≫ χ := by sorry
