-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_queryTime_gibbs
-- name    : ThreeSum.LightWeightedFrozenQuery.queryTime_gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:42.643924+00:00
-- url     : https://prove2.me/theorems/aa283be4-61a7-4234-a7f7-cfd6a7e20ec9
-- title:
--   Light Weighted Frozen Query: query Time gibbs
-- statement:
--   The Light Weighted Frozen Query construction uses the query Time gibbs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenTime.lean#L79-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenTime.lean#L79-L87

import Definitions.Def_Submission_Weighted_FrozenPrepare
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenTime
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedFrozenQueryCost
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedFrozenQuery.queryTime_gibbs {N : ℕ} (L T : ℕ) (R : TritWord N)
    (z : ℝ) (hz : 0≤z) (hz1 : z≤1) :
    (queryTime L T N R : ℝ)*z^(cacheCost R+1024-T)≤
      10000*(N+L+1)*(N+1)*(1+z^512)^digitCount R 1*(1+z^513+z^1025)^digitCount R 2 := by sorry
