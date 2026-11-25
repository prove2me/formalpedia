-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integral_log_eval_mul_le
-- name    : ReciprocityTheory.MultiplicativeHeights.integral_log_eval_mul_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:38.128899+00:00
-- url     : https://prove2.me/theorems/4ea9399d-0a78-5ade-be93-6cf79e291eed
-- title:
--   Multiplicative Heights: integral log eval mul le
-- statement:
--   The Multiplicative Heights construction uses the integral log eval mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusA.lean#L54-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusA.lean#L54-L61

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

theorem ReciprocityTheory.MultiplicativeHeights.integral_log_eval_mul_le (p : ℂ[X]) {c : ℂ} (hc : c ≠ 0) (hc1 : ‖c‖ ≤ 1) :
    ∫ t in Set.Ioc (0 : ℝ) 1,
        Real.log ‖p.eval (c * Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))‖ ≤
      ∫ t in Set.Ioc (0 : ℝ) 1, Real.log ‖p.eval (Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))‖ := by sorry
