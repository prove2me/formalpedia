-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_germ_stalkClosedPointTo_eq
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.germ_stalkClosedPointTo_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:25:44.991802+00:00
-- url     : https://prove2.me/theorems/bf6b7f84-ace6-4c43-8620-5c833788444f
-- title:
--   Pullback Sections: germ stalk Closed Point To eq
-- statement:
--   The Pullback Sections construction uses the germ stalk Closed Point To eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetA.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetA.lean#L13-L21

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.germ_stalkClosedPointTo_eq {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ Y) (U : Y.Opens)
    (hU : f (IsLocalRing.closedPoint R) ∈ U) :
    Y.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo f =
      f.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem f hU).ge ≫ (Scheme.ΓSpecIso R).hom := by sorry
