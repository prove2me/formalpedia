-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_extErr_le
-- name    : ReciprocityTheory.L2DbarEstimates.C.extErr_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:54:43.06553+00:00
-- url     : https://prove2.me/theorems/350be086-6db0-42d1-820a-03cc85f25e2c
-- title:
--   C: ext Err le
-- statement:
--   The C construction uses the ext Err le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeak.lean#L77-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeak.lean#L77-L121

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCut
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeak
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollifyEqConvolution
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeak
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

theorem ReciprocityTheory.L2DbarEstimates.C.extErr_le {F g u : V n → ℂ} {k C0 Mg : ℝ} (hk : 0 < k) (hC0 : 0 ≤ C0)
    (hC0b : ∀ t, ‖deriv extCh t‖ ≤ C0) (hMg : ∀ z, ‖g z‖ ≤ Mg) {z : V n} (v : V n)
    (hFd : DifferentiableAt ℝ F z) (hz : F z ≠ 0) :
    ‖u z * g z * extErr F k v z‖ₑ ≤ ENNReal.ofReal (Mg * (2 * ‖v‖) * C0 * k⁻¹) *
      (tsupport g ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧
        -Real.log (‖F z‖ ^ 2) ≤ 2 * k}).indicator
        (fun z => ‖u z‖ₑ * ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ) z := by sorry
