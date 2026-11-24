-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_continuous_tmax_shift
-- name    : ReciprocityTheory.AnForm.A.continuous_tmax_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:54.764125+00:00
-- url     : https://prove2.me/theorems/1695a01f-c3a0-4f68-bc6b-8fd1f3a3febf
-- title:
--   A: continuous tmax shift
-- statement:
--   The A construction uses the continuous tmax shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L176-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L176-L178

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

theorem ReciprocityTheory.AnForm.A.continuous_tmax_shift (η : ℝ) (t : ι → ℝ) :
    Continuous (fun h : ι → ℝ => tmax (fun j => t j + η * h j)) := by sorry
