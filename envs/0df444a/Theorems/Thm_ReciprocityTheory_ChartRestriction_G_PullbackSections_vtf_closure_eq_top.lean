-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_closure_eq_top
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_closure_eq_top
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:12:03.389743+00:00
-- url     : https://prove2.me/theorems/e55611bb-ef99-5ac7-bc2a-6db6a998d326
-- title:
--   Pullback Sections: vtf closure eq top
-- statement:
--   The Pullback Sections construction uses the vtf closure eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtFrRdHol.lean#L11-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtFrRdHol.lean#L11-L35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol
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
open AlgebraicGeometry CategoryTheory Limits Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_closure_eq_top {A B C P : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {inl : B ⟶ P}
    {inr : C ⟶ P} (h : IsPushout f g inl inr) :
    Subring.closure (Set.range inl.hom ∪ Set.range inr.hom) = ⊤ := by sorry
