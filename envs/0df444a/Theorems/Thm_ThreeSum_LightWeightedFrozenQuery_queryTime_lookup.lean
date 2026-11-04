-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_queryTime_lookup
-- name    : ThreeSum.LightWeightedFrozenQuery.queryTime_lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:39.580214+00:00
-- url     : https://prove2.me/theorems/791f2ccb-9a69-4400-bbb5-1063fc3b0211
-- title:
--   Light Weighted Frozen Query: query Time lookup
-- statement:
--   The Light Weighted Frozen Query construction uses the query Time lookup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenTime.lean#L27-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenTime.lean#L27-L35

import Definitions.Def_Submission_Weighted_FrozenPrepare
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenTime
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedFrozenQueryCost
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedFrozenQuery.queryTime_lookup {N : ℕ} (L T K : ℕ) (R : TritWord N) :
    LightTernaryQueryLookup.time L+100≤queryTime L T K R := by sorry
