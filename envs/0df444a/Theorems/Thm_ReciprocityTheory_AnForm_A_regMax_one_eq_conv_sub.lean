-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_one_eq_conv_sub
-- name    : ReciprocityTheory.AnForm.A.regMax_one_eq_conv_sub
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:49.993622+00:00
-- url     : https://prove2.me/theorems/b566442a-1b5b-4f6d-acd3-e25888eb715f
-- title:
--   A: reg Max one eq conv sub
-- statement:
--   The A construction uses the reg Max one eq conv sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L32-L41

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem ReciprocityTheory.AnForm.A.regMax_one_eq_conv_sub (c : ℝ) :
    regMax (ι := ι) 1 = fun x => convolution kK (fun y => tmax y - c)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume x + c := by sorry
