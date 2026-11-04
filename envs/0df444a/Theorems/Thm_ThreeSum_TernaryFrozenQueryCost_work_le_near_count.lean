-- Prove2me | Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_work_le_near_count
-- name    : ThreeSum.TernaryFrozenQueryCost.work_le_near_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:10.88522+00:00
-- url     : https://prove2.me/theorems/e19a35a5-6700-4d24-8979-d5077dad7779
-- title:
--   Ternary Frozen Query Cost: work le near count
-- statement:
--   The Ternary Frozen Query Cost construction uses the work le near count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean#L81-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean#L81-L87

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryCost
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryFrozenQueryCost.work_le_near_count {N : ℕ} (T : ℕ) (coords : List (Fin N))
    (hcoords : coords.Nodup) (R : TritWord N) :
    work T coords R≤(coords.length+1)*
      (TernaryNearEnumeration.words (caps coords R) (rank R+1-T)).length := by sorry
