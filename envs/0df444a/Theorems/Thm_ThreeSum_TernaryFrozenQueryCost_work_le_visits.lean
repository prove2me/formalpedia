-- Prove2me | Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_work_le_visits
-- name    : ThreeSum.TernaryFrozenQueryCost.work_le_visits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:06.369683+00:00
-- url     : https://prove2.me/theorems/42ea258a-e548-4a50-b7ac-2cffa8c8a299
-- title:
--   Ternary Frozen Query Cost: work le visits
-- statement:
--   One extra deficit unit permits the final trit-2 jump across the bank cutoff.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean#L56-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean#L56-L79

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryCost
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryFrozenQueryCost.work_le_visits {N : ℕ} (T : ℕ) (coords : List (Fin N))
    (hcoords : coords.Nodup) (R : TritWord N) :
    work T coords R≤TernaryNearEnumeration.visits (caps coords R) (rank R+1-T) := by sorry
