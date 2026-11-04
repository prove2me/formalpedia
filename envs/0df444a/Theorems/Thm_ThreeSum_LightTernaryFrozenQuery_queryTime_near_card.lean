-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_queryTime_near_card
-- name    : ThreeSum.LightTernaryFrozenQuery.queryTime_near_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:56.656149+00:00
-- url     : https://prove2.me/theorems/ab7f45c7-c347-4c1e-9a4e-e370143d6ab1
-- title:
--   Light Ternary Frozen Query: query Time near card
-- statement:
--   The Light Ternary Frozen Query construction uses the query Time near card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean#L49-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean#L49-L54

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPrepare
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryTime
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryFrozenQueryCost
set_option maxHeartbeats 3000000

theorem ThreeSum.LightTernaryFrozenQuery.queryTime_near_card {N : ℕ} (L T K : ℕ) (hK : K≤N) (R : TritWord N) :
    queryTime L T K R≤10000*(N+L+1)*(K+1)*
      (nearWords (capWord (coords N K) R) (rank R+1-T)).card := by sorry
