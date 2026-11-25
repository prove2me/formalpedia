-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_extCh_nonneg
-- name    : ReciprocityTheory.L2DbarEstimates.C.extCh_nonneg
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:54.530962+00:00
-- url     : https://prove2.me/theorems/160a5060-fc7d-495a-8368-df67d66f1631
-- title:
--   C: ext Ch nonneg
-- statement:
--   The C construction uses the ext Ch nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeakA.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeakA.lean#L13-L13

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

theorem ReciprocityTheory.L2DbarEstimates.C.extCh_nonneg (t : ℝ) : 0 ≤ extCh t := by sorry
