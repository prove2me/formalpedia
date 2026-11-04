-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_prefixStageTime_eq_step
-- name    : ThreeSum.WeightedGlobalActualSeedRuntime.prefixStageTime_eq_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:21:17.926013+00:00
-- url     : https://prove2.me/theorems/5f626a6d-c926-4180-a4ca-caf305a9d1f6
-- title:
--   Weighted Global Actual Seed Runtime: prefix Stage Time eq step
-- statement:
--   Equality with the actual prepare/controller/commit machine timing at
--   the next prefix; every mutable key and span copy is included.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L569-L583
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L569-L583

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_Submission_Weighted_Global_TernarySeedCoefficientBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryActualSeedRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualSeedRuntime
open Real Light Filter
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalEntropyRates WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalActualSeedRuntime.prefixStageTime_eq_step {K k m F old : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : (seed : ℕ)→LightWeightedGlobalSeedScoreFactory.Data (config (nativePrime K m) (old+1) I A seed))
    (X : LightWeightedGlobalPrefixStep.Inputs) (hm : X.m=m) (hj : X.j=old) (hp : X.p=nativePrime K m)
    (ha : X.alpha2=fixedAlpha m 2) (hpow : X.power=(nativePrime K m)^old) :
    prefixStageTime (K:=K) (k:=k) maps Q I A D=
      LightWeightedGlobalPrefixStep.time X (config (nativePrime K m) (old+1) I A 0)
        (menuSize K m A.J*menuSize K m A.J) (prefixSeedTime (K:=K) (k:=k) maps Q I A D):= by sorry
