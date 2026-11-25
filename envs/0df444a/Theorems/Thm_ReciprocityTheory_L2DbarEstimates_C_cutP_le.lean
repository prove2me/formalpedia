-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_cutP_le
-- name    : ReciprocityTheory.L2DbarEstimates.C.cutP_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:17.172485+00:00
-- url     : https://prove2.me/theorems/f2eeda2e-b1a0-4858-96f2-ed1d06511fb3
-- title:
--   C: cut P le
-- statement:
--   The C construction uses the cut P le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L73-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L73-L88

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
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
open scoped ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.C.cutP_le {k m : ℝ} (hk : 1 ≤ k) (hm : 0 ≤ m) :
    cutP (Real.exp (-2 * k)) m ≤ (m + 2) ^ 2 / 2 * k ^ 2 := by sorry
