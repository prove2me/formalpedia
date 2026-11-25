-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_circle
-- name    : ReciprocityTheory.AnForm.A.regMax_circle
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:20:43.183823+00:00
-- url     : https://prove2.me/theorems/d393ae41-8d5e-510f-8ec0-6d7a309c7525
-- title:
--   A: reg Max circle
-- statement:
--   The A construction uses the reg Max circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L177-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L177-L204

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
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

theorem ReciprocityTheory.AnForm.A.regMax_circle {η : ℝ} (hη : 0 < η) (f : ℂ → ι → ℝ) (c : ℂ) (R : ℝ)
    (hf : ∀ j, CircleIntegrable (fun ζ => f ζ j) c R) :
    CircleIntegrable (fun ζ => regMax η (f ζ)) c R ∧
      regMax η (fun j => Real.circleAverage (fun ζ => f ζ j) c R) ≤
        Real.circleAverage (fun ζ => regMax η (f ζ)) c R := by sorry
