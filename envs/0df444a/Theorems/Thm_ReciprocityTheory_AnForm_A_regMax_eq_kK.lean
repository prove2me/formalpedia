-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_eq_kK
-- name    : ReciprocityTheory.AnForm.A.regMax_eq_kK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:31.319458+00:00
-- url     : https://prove2.me/theorems/c6e00f19-6de5-4a52-a081-06ea80f14131
-- title:
--   A: reg Max eq k K
-- statement:
--   The A construction uses the reg Max eq k K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L173-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L173-L174

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

theorem ReciprocityTheory.AnForm.A.regMax_eq_kK (η : ℝ) (t : ι → ℝ) :
    regMax η t = ∫ h, tmax (fun j => t j + η * h j) * kK h := by sorry
