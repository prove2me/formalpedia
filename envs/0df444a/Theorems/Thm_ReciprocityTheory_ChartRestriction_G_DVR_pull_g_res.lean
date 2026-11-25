-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pull_g_res
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.pull_g_res
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:16:09.168284+00:00
-- url     : https://prove2.me/theorems/f8c500c7-2ca4-519a-8cf8-7837ce9b2c4f
-- title:
--   DVR: pull g res
-- statement:
--   The DVR construction uses the pull g res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenAmple.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenAmple.lean#L29-L41

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenAmple
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {Y X₁ X₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)

theorem ReciprocityTheory.ChartRestriction.G.DVR.pull_g_res {X : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (a b : PUnit → L.ι) {V : Y.Opens}
    (h : V ≤ (L.pull f).U a ⊓ (L.pull f).U b) : res h ((L.pull f).g a b) = tr L V f (a PUnit.unit) (b PUnit.unit) := by sorry
