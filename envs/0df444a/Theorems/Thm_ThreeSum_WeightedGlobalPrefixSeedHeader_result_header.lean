-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrefixSeedHeader_result_header
-- name    : ThreeSum.WeightedGlobalPrefixSeedHeader.result_header
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:08:59.672862+00:00
-- url     : https://prove2.me/theorems/7d178dd1-9106-4867-a9ba-7fe41b06a5f8
-- title:
--   Weighted Global Prefix Seed Header: result header
-- statement:
--   The computed writes are exactly the next controller ABI.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean#L54-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean#L54-L58

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrefixSeedHeader
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open LightWeightedGlobalPrefixStep LightWeightedGlobalPrefixHeader LightWeightedGlobalPrefixFinish
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalPrefixSeedHeader.result_header (C : Config) (X : Inputs) (n dB dC dP tB tC tP newSpan : ℕ) :
    result (header C n dB dC dP tB tC tP newSpan) X=
      header (nextConfig C X) n (X.xB*X.p) (X.xC*X.p) (X.xP*X.a) (X.tB*9) (X.tC*9)
        (X.tP*X.b*X.scale) newSpan := by sorry
