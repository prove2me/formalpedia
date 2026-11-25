-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_cmpb_det_nonneg
-- name    : ReciprocityTheory.L2DbarEstimates.Y.cmpb_det_nonneg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:09.250387+00:00
-- url     : https://prove2.me/theorems/a7d41a10-5663-50af-9511-cb0ec58d99bf
-- title:
--   Y: cmpb det nonneg
-- statement:
--   The Y construction uses the cmpb det nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/CmpbHessAtAddConst.lean#L45-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/CmpbHessAtAddConst.lean#L45-L136

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetUpdateColEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpaCHessComp
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpbHessAtAddConst
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re

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

theorem ReciprocityTheory.L2DbarEstimates.Y.cmpb_det_nonneg {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hL : ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => ((f v : ℝ) : ℂ)) x ξ).re) :
    0 ≤ (cHess n (fun v => ((f v : ℝ) : ℂ)) x).det.re := by sorry
