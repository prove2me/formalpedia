-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_integral_affine_kK
-- name    : ReciprocityTheory.AnForm.A.integral_affine_kK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:14.660131+00:00
-- url     : https://prove2.me/theorems/3b2c6c15-0de6-4109-9fef-8e3d2b47b7bf
-- title:
--   A: integral affine k K
-- statement:
--   The A construction uses the integral affine k K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L145-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L145-L154

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
variable {ι : Type*} [Fintype ι]

theorem ReciprocityTheory.AnForm.A.integral_affine_kK (c a : ℝ) (i : ι) : ∫ h, (c + a * h i) * kK h = c := by sorry
