-- Prove2me | Theorems.Thm_ThreeSum_WeightedFrozenQueryCost_work_le_capWord_card
-- name    : ThreeSum.WeightedFrozenQueryCost.work_le_capWord_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:22:47.007904+00:00
-- url     : https://prove2.me/theorems/1bbb9331-f1ac-40a3-b0a4-4f4945b73338
-- title:
--   Weighted Frozen Query Cost: work le cap Word card
-- statement:
--   The Weighted Frozen Query Cost construction uses the work le cap Word card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L122-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L122-L129

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_work_le_capWord_card

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration

theorem ThreeSum.WeightedFrozenQueryCost.work_le_capWord_card {N : ℕ} (T : ℕ) (coords : List (Fin N))
    (hcoords : coords.Nodup) (R : Word N) :
    work T coords R≤(coords.length+1)*
      (WeightedNearBankEnumeration.nearWords (capWord coords R) (cacheCost R+1024-T)).card := by sorry
