-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalGlobalPreludeResources_parameter_bound
-- name    : ThreeSum.WeightedGlobalGlobalPreludeResources.parameter_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:03:00.053536+00:00
-- url     : https://prove2.me/theorems/617a97f8-b657-4e5f-bc38-b734dc10ba3f
-- title:
--   Weighted Global Global Prelude Resources: parameter bound
-- statement:
--   The Weighted Global Global Prelude Resources construction uses the parameter bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGlobalPreludeResources.lean#L67-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGlobalPreludeResources.lean#L67-L78

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

theorem ThreeSum.WeightedGlobalGlobalPreludeResources.parameter_bound {M b p K : ℕ} [Fact p.Prime] (hM : 1<M) (hb : 1<b) (κ n : ℕ) :
    LightExtensionBackendLayout.params
      (LightWeightedGlobalDimensions.dim M b p K n (n^κ)) p
      (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ))) (LightWeightedGlobalDimensions.J M b n (n^κ))≤
        baseCoefficient M b p K*(n+1)^(κ+2) := by sorry
