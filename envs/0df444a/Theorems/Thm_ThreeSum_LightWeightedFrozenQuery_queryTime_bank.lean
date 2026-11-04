-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_queryTime_bank
-- name    : ThreeSum.LightWeightedFrozenQuery.queryTime_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:51:59.680248+00:00
-- url     : https://prove2.me/theorems/815f14ac-6afa-4a3f-b921-1d5f5e11ff1d
-- title:
--   Light Weighted Frozen Query: query Time bank
-- statement:
--   The Light Weighted Frozen Query construction uses the query Time bank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenTime.lean#L24-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenTime.lean#L24-L25

import Definitions.Def_Submission_Weighted_FrozenPrepare
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenTime
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedFrozenQueryCost
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedFrozenQuery.queryTime_bank {N : ℕ} (L T K : ℕ) (R : TritWord N) (h : cacheCost R≤T) :
    queryTime L T K R=10000*(N+L+1) := by sorry
