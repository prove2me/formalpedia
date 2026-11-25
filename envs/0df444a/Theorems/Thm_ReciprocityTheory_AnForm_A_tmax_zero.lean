-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_zero
-- name    : ReciprocityTheory.AnForm.A.tmax_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:24.191617+00:00
-- url     : https://prove2.me/theorems/82f1d0e7-8f84-4506-8c9c-9d949fc178e7
-- title:
--   A: tmax zero
-- statement:
--   The A construction uses the tmax zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L153-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L153-L154

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

theorem ReciprocityTheory.AnForm.A.tmax_zero : tmax (0 : ι → ℝ) = 0 := by sorry
