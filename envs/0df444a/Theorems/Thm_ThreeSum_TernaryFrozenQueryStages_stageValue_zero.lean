-- Prove2me | Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
-- name    : ThreeSum.TernaryFrozenQueryStages.stageValue_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:40:50.546547+00:00
-- url     : https://prove2.me/theorems/0a61aaf3-77f8-42be-9bb6-acd01af20eb2
-- title:
--   Ternary Frozen Query Stages: stage Value zero
-- statement:
--   The Ternary Frozen Query Stages construction uses the stage Value zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryStages.lean#L32-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryStages.lean#L32-L33

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryFrozenQueryStages.stageValue_zero {N : ℕ} (H : TritWord N→ℤ) : stageValue 0 H=H := by sorry
