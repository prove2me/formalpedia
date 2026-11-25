-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_fderiv_logCutoff_eq_zero
-- name    : ReciprocityTheory.L2DbarEstimates.C.fderiv_logCutoff_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:43.20893+00:00
-- url     : https://prove2.me/theorems/93635265-a701-5034-9ace-9c615bcbfdef
-- title:
--   C: fderiv log Cutoff eq zero
-- statement:
--   The C construction uses the fderiv log Cutoff eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeakA.lean#L170-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeakA.lean#L170-L184

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.C.fderiv_logCutoff_eq_zero {F : V n → ℂ} {k : ℝ} (hk : 0 < k) {z : V n}
    (hF : DifferentiableAt ℝ F z) (hz : F z ≠ 0)
    (h : ¬ (k ≤ -Real.log (‖F z‖ ^ 2) ∧ -Real.log (‖F z‖ ^ 2) ≤ 2 * k)) :
    fderiv ℝ (extCut F k) z = 0 := by sorry
