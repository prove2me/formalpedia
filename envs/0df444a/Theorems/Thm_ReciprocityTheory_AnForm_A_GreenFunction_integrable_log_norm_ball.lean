-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_integrable_log_norm_ball
-- name    : ReciprocityTheory.AnForm.A.GreenFunction.integrable_log_norm_ball
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:34.769495+00:00
-- url     : https://prove2.me/theorems/3aa2a5ed-2952-489b-a7e4-acff015c3985
-- title:
--   Green Function: integrable log norm ball
-- statement:
--   The Green Function construction uses the integrable log norm ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L233-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenPolar.lean#L233-L250

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology InnerProductSpace intervalIntegral
open scoped Laplacian
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.GreenFunction
noncomputable section

theorem ReciprocityTheory.AnForm.A.GreenFunction.integrable_log_norm_ball {R : ℝ} (hR0 : 0 < R) :
    Integrable (fun z : ℂ => (Iic R).indicator (fun t => ‖Real.log t‖) ‖z‖) := by sorry
