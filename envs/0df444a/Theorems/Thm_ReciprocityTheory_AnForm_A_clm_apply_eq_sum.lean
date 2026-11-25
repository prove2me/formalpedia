-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_clm_apply_eq_sum
-- name    : ReciprocityTheory.AnForm.A.clm_apply_eq_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:43.701612+00:00
-- url     : https://prove2.me/theorems/fe327a75-dd59-5b01-a453-1b6bec25ef2a
-- title:
--   A: clm apply eq sum
-- statement:
--   The A construction uses the clm apply eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L320-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L320-L327

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem ReciprocityTheory.AnForm.A.clm_apply_eq_sum [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℝ) (c : ι → ℝ) :
    L c = ∑ j, c j * L (Pi.single j 1) := by sorry
