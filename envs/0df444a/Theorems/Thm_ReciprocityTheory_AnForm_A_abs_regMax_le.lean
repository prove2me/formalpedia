-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_abs_regMax_le
-- name    : ReciprocityTheory.AnForm.A.abs_regMax_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:46.065918+00:00
-- url     : https://prove2.me/theorems/8b94810e-c59d-42ca-b4a8-25f3b910c4f7
-- title:
--   A: abs reg Max le
-- statement:
--   The A construction uses the abs reg Max le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L156-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L156-L161

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

theorem ReciprocityTheory.AnForm.A.abs_regMax_le {η : ℝ} (hη : 0 ≤ η) (v : ι → ℝ) : |regMax η v| ≤ ‖v‖ + η / 2 := by sorry
