-- Prove2me | Theorems.Thm_ThreeSum_WeightedFrozenQueryCost_work_le_enumerated_queries
-- name    : ThreeSum.WeightedFrozenQueryCost.work_le_enumerated_queries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:13:14.495866+00:00
-- url     : https://prove2.me/theorems/4c0f8b74-1250-4717-a833-e18134a8cdf7
-- title:
--   Weighted Frozen Query Cost: work le enumerated queries
-- statement:
--   The Weighted Frozen Query Cost construction uses the work le enumerated queries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L107-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L107-L113

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenQueryCost
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration

theorem ThreeSum.WeightedFrozenQueryCost.work_le_enumerated_queries {N : ℕ} (T : ℕ) (coords : List (Fin N))
    (hcoords : coords.Nodup) (R : Word N) :
    work T coords R ≤ (coords.length+1) *
      (WeightedNearEnumeration.codes (caps coords R) (cacheCost R+1024-T)).length := by sorry
