-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_mem_finset_inf
-- name    : ReciprocityTheory.ChartRestriction.G.Out.WeightPf.mem_finset_inf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:25:00.689373+00:00
-- url     : https://prove2.me/theorems/3db255d7-371d-4898-a9ba-e4691a317e5a
-- title:
--   Weight Pf: mem finset inf
-- statement:
--   The Weight Pf construction uses the mem finset inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/WeightIndep.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/WeightIndep.lean#L22-L29

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

theorem ReciprocityTheory.ChartRestriction.G.Out.WeightPf.mem_finset_inf {Y : Scheme.{0}} {κ : Type} (s : Finset κ) (F : κ → Y.Opens) (y : Y)
    (h : ∀ i ∈ s, y ∈ F i) : y ∈ s.inf F := by sorry
