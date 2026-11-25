-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_weightIndep
-- name    : ReciprocityTheory.ChartRestriction.G.Out.WeightPf.weightIndep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:45.749032+00:00
-- url     : https://prove2.me/theorems/82694dad-7419-4081-9b47-a7124eb2dee4
-- title:
--   Weight Pf: weight Indep
-- statement:
--   The Weight Pf construction uses the weight Indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/WeightIndep.lean#L40-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/WeightIndep.lean#L40-L224

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WeightIndep
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.WeightPf
open Semi
set_option maxHeartbeats 1000000

theorem ReciprocityTheory.ChartRestriction.G.Out.WeightPf.weightIndep : WeightIndepSt := by sorry
