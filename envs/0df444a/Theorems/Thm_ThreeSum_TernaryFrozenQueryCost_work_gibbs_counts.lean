-- Prove2me | Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_work_gibbs_counts
-- name    : ThreeSum.TernaryFrozenQueryCost.work_gibbs_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:17.814544+00:00
-- url     : https://prove2.me/theorems/6897d8f7-2899-4a05-94f8-88c6054a78f6
-- title:
--   Ternary Frozen Query Cost: work gibbs counts
-- statement:
--   The Ternary Frozen Query Cost construction uses the work gibbs counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean#L112-L130
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean#L112-L130

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryCost
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryFrozenQueryCost.work_gibbs_counts {N : ℕ} (T : ℕ) (coords : List (Fin N))
    (hcoords : coords.Nodup) (R : TritWord N) (z : ℝ) (hz : 0≤z) (hz1 : z≤1) :
    (work T coords R : ℝ)*z^(rank R+1-T) ≤
      (coords.length+1)*(1+z)^digitCount (capWord coords R) 1 *
        (1+z+z^2)^digitCount (capWord coords R) 2 := by sorry
