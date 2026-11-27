-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_cmpb_cHess_add_const
-- name    : ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_add_const
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:59.614237+00:00
-- url     : https://prove2.me/theorems/0149bc00-37c2-519e-97c0-c14975ad4167
-- title:
--   Y: cmpb c Hess add const
-- statement:
--   The Y construction uses the cmpb c Hess add const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/CmpbHessAtAddConst.lean#L157-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/CmpbHessAtAddConst.lean#L157-L162

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetUpdateColEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpaCHessComp
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpbHessAtAddConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Complex ComplexConjugate
open scoped ContDiff ENNReal ComplexOrder
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
universe u
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_add_const (g : V n → ℂ) (c : ℂ) (x : V n) :
    cHess n (fun v => g v + c) x = cHess n g x := by sorry
