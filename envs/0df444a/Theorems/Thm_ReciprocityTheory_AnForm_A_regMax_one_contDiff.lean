-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_one_contDiff
-- name    : ReciprocityTheory.AnForm.A.regMax_one_contDiff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:38.971912+00:00
-- url     : https://prove2.me/theorems/2a6cf68e-b54e-4430-90ad-bcd777a3bd23
-- title:
--   A: reg Max one cont Diff
-- statement:
--   The A construction uses the reg Max one cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L352-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L352-L355

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

theorem ReciprocityTheory.AnForm.A.regMax_one_contDiff : ContDiff ℝ ∞ (regMax (ι := ι) 1) := by sorry
