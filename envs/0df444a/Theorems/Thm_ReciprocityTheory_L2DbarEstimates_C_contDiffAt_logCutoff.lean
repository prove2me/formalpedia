-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_contDiffAt_logCutoff
-- name    : ReciprocityTheory.L2DbarEstimates.C.contDiffAt_logCutoff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:12.541482+00:00
-- url     : https://prove2.me/theorems/3836b170-738e-4645-a1fe-30225eb71ff5
-- title:
--   C: cont Diff At log Cutoff
-- statement:
--   The C construction uses the cont Diff At log Cutoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeakA.lean#L92-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeakA.lean#L92-L105

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

theorem ReciprocityTheory.L2DbarEstimates.C.contDiffAt_logCutoff {F : V n → ℂ} {k : ℝ} (hk : 0 < k) {z : V n}
    (hF : ContDiffAt ℝ ∞ F z) : ContDiffAt ℝ ∞ (extCut F k) z := by sorry
