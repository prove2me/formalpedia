-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integral_Ioc_log_eval_eq_logMahlerMeasure
-- name    : ReciprocityTheory.MultiplicativeHeights.integral_Ioc_log_eval_eq_logMahlerMeasure
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:32.576336+00:00
-- url     : https://prove2.me/theorems/20a1c0e0-0a54-5e04-bc0d-a2e97c377cdd
-- title:
--   Multiplicative Heights: integral Ioc log eval eq log Mahler Measure
-- statement:
--   The Multiplicative Heights construction uses the integral Ioc log eval eq log Mahler Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusA.lean#L9-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusA.lean#L9-L23

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Polynomial

theorem ReciprocityTheory.MultiplicativeHeights.integral_Ioc_log_eval_eq_logMahlerMeasure (q : ℂ[X]) :
    ∫ t in Set.Ioc (0 : ℝ) 1, Real.log ‖q.eval (Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))‖ =
      q.logMahlerMeasure := by sorry
