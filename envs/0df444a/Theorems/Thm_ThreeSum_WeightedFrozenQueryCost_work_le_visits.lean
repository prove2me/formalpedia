-- Prove2me | Theorems.Thm_ThreeSum_WeightedFrozenQueryCost_work_le_visits
-- name    : ThreeSum.WeightedFrozenQueryCost.work_le_visits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:16:28.864803+00:00
-- url     : https://prove2.me/theorems/702aa502-05fc-4f1c-b41e-b0d107e5b600
-- title:
--   Weighted Frozen Query Cost: work le visits
-- statement:
--   A jump from digit 2 to 0 can cost 1025. The final crossing therefore
--   requires 1024 extra deficit units, not the old one-unit overshoot.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L81-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L81-L105

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_work_le_visits

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration

theorem ThreeSum.WeightedFrozenQueryCost.work_le_visits {N : ℕ} (T : ℕ) (coords : List (Fin N))
    (hcoords : coords.Nodup) (R : Word N) :
    work T coords R ≤ WeightedNearEnumeration.visits (caps coords R)
      (cacheCost R+1024-T) := by sorry
