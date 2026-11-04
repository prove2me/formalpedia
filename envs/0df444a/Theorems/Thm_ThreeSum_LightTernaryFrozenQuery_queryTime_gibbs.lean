-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_queryTime_gibbs
-- name    : ThreeSum.LightTernaryFrozenQuery.queryTime_gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:54.093113+00:00
-- url     : https://prove2.me/theorems/7b17cfe6-73a6-4b6e-8b09-0bad600430aa
-- title:
--   Light Ternary Frozen Query: query Time gibbs
-- statement:
--   The Light Ternary Frozen Query construction uses the query Time gibbs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean#L73-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean#L73-L81

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPrepare
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryTime
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryFrozenQueryCost
set_option maxHeartbeats 3000000

theorem ThreeSum.LightTernaryFrozenQuery.queryTime_gibbs {N : ℕ} (L T : ℕ) (R : TritWord N)
    (z : ℝ) (hz : 0≤z) (hz1 : z≤1) :
    (queryTime L T N R : ℝ)*z^(rank R+1-T)≤
      10000*(N+L+1)*(N+1)*(1+z)^digitCount R 1*(1+z+z^2)^digitCount R 2 := by sorry
