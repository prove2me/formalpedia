-- Prove2me | Theorems.Thm_ThreeSum_WeightedFrozenQueryCost_work_gibbs_counts
-- name    : ThreeSum.WeightedFrozenQueryCost.work_gibbs_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:25:22.717072+00:00
-- url     : https://prove2.me/theorems/c18e4d3d-163d-4939-b217-00f189f0529b
-- title:
--   Weighted Frozen Query Cost: work gibbs counts
-- statement:
--   The Weighted Frozen Query Cost construction uses the work gibbs counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L144-L171
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L144-L171

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_work_gibbs_counts

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration

theorem ThreeSum.WeightedFrozenQueryCost.work_gibbs_counts {N : ℕ} (T : ℕ) (coords : List (Fin N))
    (hcoords : coords.Nodup) (R : Word N) (z : ℝ) (hz : 0≤z) (hz1 : z≤1) :
    (work T coords R : ℝ)*z^(cacheCost R+1024-T) ≤
      (coords.length+1)*(1+z^512)^TernaryJointType.digitCount (capWord coords R) 1 *
        (1+z^513+z^1025)^TernaryJointType.digitCount (capWord coords R) 2 := by sorry
