-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_queryTime_lookup
-- name    : ThreeSum.LightTernaryFrozenQuery.queryTime_lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:32:38.205783+00:00
-- url     : https://prove2.me/theorems/98f8a3ce-e567-4e73-8642-728e567a9307
-- title:
--   Light Ternary Frozen Query: query Time lookup
-- statement:
--   The Light Ternary Frozen Query construction uses the query Time lookup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean#L21-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean#L21-L29

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPrepare
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryTime
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryFrozenQueryCost
set_option maxHeartbeats 3000000

theorem ThreeSum.LightTernaryFrozenQuery.queryTime_lookup {N : ℕ} (L T K : ℕ) (R : TritWord N) :
    LightTernaryQueryLookup.time L+100≤queryTime L T K R := by sorry
