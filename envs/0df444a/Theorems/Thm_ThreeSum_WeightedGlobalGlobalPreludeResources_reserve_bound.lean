-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalGlobalPreludeResources_reserve_bound
-- name    : ThreeSum.WeightedGlobalGlobalPreludeResources.reserve_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:03:28.702874+00:00
-- url     : https://prove2.me/theorems/6dce5ee0-8baf-4f96-ae5f-8506ea10925c
-- title:
--   Weighted Global Global Prelude Resources: reserve bound
-- statement:
--   The Weighted Global Global Prelude Resources construction uses the reserve bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGlobalPreludeResources.lean#L80-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGlobalPreludeResources.lean#L80-L89

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryGlobalPreludeProof
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsBudget
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_Weighted_Global_TernaryGlobalPreludeResources
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalGlobalPreludeResources
open Light LightWeightedGlobalGlobalPrelude
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalGlobalPreludeResources.reserve_bound {M b p K : ℕ} [Fact p.Prime] (hM : 1<M) (hb : 1<b) (κ n : ℕ) :
    LightExtensionBackendLayout.reserve
      (LightWeightedGlobalDimensions.dim M b p K n (n^κ)) p
      (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ))) (LightWeightedGlobalDimensions.J M b n (n^κ))≤
        100000000*(baseCoefficient M b p K)^6*(n+1)^(exponent κ) := by sorry
