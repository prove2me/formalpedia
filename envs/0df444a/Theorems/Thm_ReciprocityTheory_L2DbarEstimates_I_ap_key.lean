-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_key
-- name    : ReciprocityTheory.L2DbarEstimates.I.ap_key
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:58:24.265322+00:00
-- url     : https://prove2.me/theorems/921295b7-4a25-46ee-b3de-e53c404ab4e2
-- title:
--   I: ap key
-- statement:
--   The I construction uses the ap key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyC.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyC.lean#L8-L15

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem ReciprocityTheory.L2DbarEstimates.I.ap_key (η D : ℝ) (h8 : 8 ≤ η) (hD : 2 * η ≤ D) : 4 / η ^ 2 ≤ 1 / η - 1 / D := by sorry
