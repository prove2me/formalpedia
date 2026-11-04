-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_queryTime_bank
-- name    : ThreeSum.LightTernaryFrozenQuery.queryTime_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:53:08.5821+00:00
-- url     : https://prove2.me/theorems/d7b53971-0039-44ba-8fd9-64aa646d8be4
-- title:
--   Light Ternary Frozen Query: query Time bank
-- statement:
--   The Light Ternary Frozen Query construction uses the query Time bank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean#L18-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean#L18-L19

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPrepare
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryTime
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryFrozenQueryCost
set_option maxHeartbeats 3000000

theorem ThreeSum.LightTernaryFrozenQuery.queryTime_bank {N : ℕ} (L T K : ℕ) (R : TritWord N) (h : rank R≤T) :
    queryTime L T K R=10000*(N+L+1) := by sorry
