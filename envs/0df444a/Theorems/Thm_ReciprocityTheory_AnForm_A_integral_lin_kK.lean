-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_integral_lin_kK
-- name    : ReciprocityTheory.AnForm.A.integral_lin_kK
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:05.013953+00:00
-- url     : https://prove2.me/theorems/31b0b6a6-469e-4554-91c5-d91d44f7b129
-- title:
--   A: integral lin k K
-- statement:
--   The A construction uses the integral lin k K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L200-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L200-L208

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

theorem ReciprocityTheory.AnForm.A.integral_lin_kK {F G : (ι → ℝ) → ℝ} (hF : Continuous F) (hG : Continuous G) (a b : ℝ) :
    ∫ h, (a * F h + b * G h) * kK h = a * (∫ h, F h * kK h) + b * (∫ h, G h * kK h) := by sorry
