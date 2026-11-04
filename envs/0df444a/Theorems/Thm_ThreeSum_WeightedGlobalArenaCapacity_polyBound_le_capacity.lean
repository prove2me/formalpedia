-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaCapacity_polyBound_le_capacity
-- name    : ThreeSum.WeightedGlobalArenaCapacity.polyBound_le_capacity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:45:34.165906+00:00
-- url     : https://prove2.me/theorems/7b92cdb4-5331-40ab-8e92-0e2f2f28dfce
-- title:
--   Weighted Global Arena Capacity: poly Bound le capacity
-- statement:
--   The Weighted Global Arena Capacity construction uses the poly Bound le capacity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCapacity.lean#L16-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCapacity.lean#L16-L25

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCapacity
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalArenaCapacity
open Light WeightedGlobalArenaLayout

theorem ThreeSum.WeightedGlobalArenaCapacity.polyBound_le_capacity (s k n U : ℕ) :
    polyBound s k [n,U]≤capacity (2^s) (2*k) (n+U) := by sorry
