-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integral_log_circ
-- name    : ReciprocityTheory.MultiplicativeHeights.integral_log_circ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:49.6098+00:00
-- url     : https://prove2.me/theorems/da6080b3-88c7-458b-af57-7c505cc83538
-- title:
--   Multiplicative Heights: integral log circ
-- statement:
--   The Multiplicative Heights construction uses the integral log circ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanA.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanA.lean#L30-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
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
open MeasureTheory Polynomial Real

theorem ReciprocityTheory.MultiplicativeHeights.integral_log_circ (p : ℂ[X]) :
    ∫ t in Set.Ioc (0 : ℝ) 1, Real.log ‖p.eval (circPt t)‖ = p.logMahlerMeasure := by sorry
