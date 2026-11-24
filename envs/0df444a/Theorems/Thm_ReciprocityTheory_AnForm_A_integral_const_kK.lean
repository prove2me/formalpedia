-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_integral_const_kK
-- name    : ReciprocityTheory.AnForm.A.integral_const_kK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:02.415193+00:00
-- url     : https://prove2.me/theorems/403a2bfa-3353-4644-84ee-f0579e1b7b73
-- title:
--   A: integral const k K
-- statement:
--   The A construction uses the integral const k K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L195-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L195-L198

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

theorem ReciprocityTheory.AnForm.A.integral_const_kK (c : ℝ) : ∫ h : ι → ℝ, c * kK h = c := by sorry
