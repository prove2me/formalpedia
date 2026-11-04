-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_queryTime_near_card
-- name    : ThreeSum.LightWeightedFrozenQuery.queryTime_near_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:38.967058+00:00
-- url     : https://prove2.me/theorems/fecad91a-982a-4c85-91bf-998da9b7f33c
-- title:
--   Light Weighted Frozen Query: query Time near card
-- statement:
--   The Light Weighted Frozen Query construction uses the query Time near card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenTime.lean#L55-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenTime.lean#L55-L60

import Definitions.Def_Submission_Weighted_FrozenPrepare
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenTime
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedFrozenQueryCost
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedFrozenQuery.queryTime_near_card {N : ℕ} (L T K : ℕ) (hK : K≤N) (R : TritWord N) :
    queryTime L T K R≤10000*(N+L+1)*(K+1)*
      (WeightedNearBankEnumeration.nearWords (capWord (coords N K) R) (cacheCost R+1024-T)).card := by sorry
