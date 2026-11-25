-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_abs_le_of_kK_ne
-- name    : ReciprocityTheory.AnForm.A.abs_le_of_kK_ne
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:34.201449+00:00
-- url     : https://prove2.me/theorems/4eb2465c-36ca-5a97-a7d8-d5400c768f2b
-- title:
--   A: abs le of k K ne
-- statement:
--   The A construction uses the abs le of k K ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L161-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L161-L164

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
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

theorem ReciprocityTheory.AnForm.A.abs_le_of_kK_ne {h : ι → ℝ} (hh : kK h ≠ 0) (j : ι) : |h j| ≤ 1 / 2 := by sorry
