-- Prove2me | Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_work_le_capWord_card
-- name    : ThreeSum.TernaryFrozenQueryCost.work_le_capWord_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:20.317668+00:00
-- url     : https://prove2.me/theorems/c5b32cd8-1bfc-45a9-8497-fbb6bd913df1
-- title:
--   Ternary Frozen Query Cost: work le cap Word card
-- statement:
--   The Ternary Frozen Query Cost construction uses the work le cap Word card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean#L102-L110
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean#L102-L110

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryCost
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryFrozenQueryCost.work_le_capWord_card {N : ℕ} (T : ℕ) (coords : List (Fin N))
    (hcoords : coords.Nodup) (R : TritWord N) :
    work T coords R≤(coords.length+1)*(nearWords (capWord coords R) (rank R+1-T)).card := by sorry
