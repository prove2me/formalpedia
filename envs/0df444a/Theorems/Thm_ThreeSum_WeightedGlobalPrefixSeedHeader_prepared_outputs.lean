-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrefixSeedHeader_prepared_outputs
-- name    : ThreeSum.WeightedGlobalPrefixSeedHeader.prepared_outputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:17:11.859445+00:00
-- url     : https://prove2.me/theorems/ace90ca1-5ff0-4050-a294-9022ccc5f9bc
-- title:
--   Weighted Global Prefix Seed Header: prepared outputs
-- statement:
--   Every physically emitted bank/header/power cell is retained by the
--   subsequent low-address scalar writes in entry184.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean#L86-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean#L86-L112

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

theorem ThreeSum.WeightedGlobalPrefixSeedHeader.prepared_outputs {X : Inputs} {μ ν : ℕ→ℤ}
    (H : Prepared X μ ν) (hhost : X.liveHeader+106≤X.seed)
    (hseed : X.seed+48≤X.prefixFree) :
    Seg ν (LightWeightedGlobalPrefixSetup.headerAt X.prefixFree X.m (X.j+1))
      (LightWeightedGlobalPrefixSetup.header X.m (X.j+1) X.F X.prefixFree
        (LightWeightedGlobalPrefixSetup.workAt X.prefixFree X.m (X.j+1))) ∧
    Seg ν X.prefixFree ((WeightedAddresses.codes (LightWeightedGlobalPrefixSetup.N X.m (X.j+1))
      (LightWeightedGlobalPrefixSetup.T X.m (X.j+1))).map (fun (c:ℕ)=>(c:ℤ))) ∧
    LightSubsetAddress.Powers ν (LightWeightedGlobalPrefixSetup.workAt X.prefixFree X.m (X.j+1))
      (2*LightWeightedGlobalPrefixSetup.N X.m (X.j+1)) := by sorry
