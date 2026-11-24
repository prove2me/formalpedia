-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_eq_fun
-- name    : ReciprocityTheory.AnForm.A.regMax_eq_fun
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:42.408809+00:00
-- url     : https://prove2.me/theorems/22d4b93b-1aa5-4493-8834-5d8f0f2802c0
-- title:
--   A: reg Max eq fun
-- statement:
--   The A construction uses the reg Max eq fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L357-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L357-L358

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

theorem ReciprocityTheory.AnForm.A.regMax_eq_fun {η : ℝ} (hη : 0 < η) :
    regMax (ι := ι) η = fun t => η * regMax 1 (η⁻¹ • t) := by sorry
