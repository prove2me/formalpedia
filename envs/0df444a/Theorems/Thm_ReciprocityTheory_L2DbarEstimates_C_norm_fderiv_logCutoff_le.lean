-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_norm_fderiv_logCutoff_le
-- name    : ReciprocityTheory.L2DbarEstimates.C.norm_fderiv_logCutoff_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:59.590922+00:00
-- url     : https://prove2.me/theorems/255e79c9-2cc8-4275-b64e-2b4c568af005
-- title:
--   C: norm fderiv log Cutoff le
-- statement:
--   The C construction uses the norm fderiv log Cutoff le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeakA.lean#L162-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeakA.lean#L162-L168

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

theorem ReciprocityTheory.L2DbarEstimates.C.norm_fderiv_logCutoff_le {F : V n → ℂ} {k C : ℝ} (hk : 0 < k)
    (hC : ∀ t, ‖deriv extCh t‖ ≤ C) {z : V n} (hF : DifferentiableAt ℝ F z) (hz : F z ≠ 0) :
    ‖fderiv ℝ (extCut F k) z‖ ≤ C * k⁻¹ * ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ := by sorry
