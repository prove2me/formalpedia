-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_update
-- name    : ReciprocityTheory.AnForm.A.regMax_update
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:14.191273+00:00
-- url     : https://prove2.me/theorems/855f6223-c2f7-4ca9-8c01-ed51cd2a1b64
-- title:
--   A: reg Max update
-- statement:
--   The A construction uses the reg Max update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L245-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L245-L263

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

theorem ReciprocityTheory.AnForm.A.regMax_update [DecidableEq ι] {η : ℝ} (hη : 0 ≤ η) (t : ι → ℝ) (j k : ι) (s : ℝ)
    (hkj : k ≠ j) (htj : t j + η ≤ t k) (hs : s + η ≤ t k) :
    regMax η (Function.update t j s) = regMax η t := by sorry
