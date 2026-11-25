-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_abs_tmax_sub_le
-- name    : ReciprocityTheory.AnForm.A.abs_tmax_sub_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:38.057843+00:00
-- url     : https://prove2.me/theorems/7629fc2d-09fe-48b3-af54-9f10d6f418cc
-- title:
--   A: abs tmax sub le
-- statement:
--   The A construction uses the abs tmax sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L52-L56

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

theorem ReciprocityTheory.AnForm.A.abs_tmax_sub_le (s t : ι → ℝ) : |tmax s - tmax t| ≤ ‖s - t‖ := by sorry
