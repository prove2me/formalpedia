-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_contDiff
-- name    : ReciprocityTheory.AnForm.A.regMax_contDiff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:48.931796+00:00
-- url     : https://prove2.me/theorems/f2d450c7-9f13-4ffe-8bcd-186374976dd6
-- title:
--   A: reg Max cont Diff
-- statement:
--   The A construction uses the reg Max cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L360-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L360-L362

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

theorem ReciprocityTheory.AnForm.A.regMax_contDiff {η : ℝ} (hη : 0 < η) : ContDiff ℝ ∞ (regMax (ι := ι) η) := by sorry
