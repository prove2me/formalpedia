-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_bound
-- name    : ReciprocityTheory.L2DbarEstimates.I.ap_bound
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:57:37.687846+00:00
-- url     : https://prove2.me/theorems/420c8042-a8b5-554d-ab20-c05e1e90621e
-- title:
--   I: ap bound
-- statement:
--   The I construction uses the ap bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyC.lean#L48-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyC.lean#L48-L67

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

theorem ReciprocityTheory.L2DbarEstimates.I.ap_bound (D ε η Θ : ℝ) (G B : ℂ) (hε : 0 < ε) (hD : |D| ≤ 3)
    (hB : ‖B‖ ^ 2 ≤ 4 * ε ^ 4 * η * Θ) (hη : 0 ≤ η) (hΘ : 0 ≤ Θ) :
    ‖((D * (1 / ε ^ 2) : ℝ) : ℂ) * G * B‖ ^ 2 ≤ 36 * η * ‖G‖ ^ 2 * Θ := by sorry
