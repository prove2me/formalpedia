-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrefixSeedHeader_prepared_kept_regions
-- name    : ThreeSum.WeightedGlobalPrefixSeedHeader.prepared_kept_regions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:11:13.372056+00:00
-- url     : https://prove2.me/theorems/edaefbc1-631e-4b24-b26b-5cc4810d6f20
-- title:
--   Weighted Global Prefix Seed Header: prepared kept regions
-- statement:
--   Every old key, retained catalog entry and original immutable input
--   survives the actual bank/header/budget preparation.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean#L73-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean#L73-L82

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

theorem ThreeSum.WeightedGlobalPrefixSeedHeader.prepared_kept_regions {X : Inputs} {μ ν : ℕ→ℤ}
    (H : Prepared X μ ν) (x : ℕ) (hp : x<X.prefixFree)
    (hhost : x<X.liveHeader ∨ X.liveHeader+106≤x)
    (hseed : x<X.seed ∨ X.seed+48≤x) : ν x=μ x := by sorry
