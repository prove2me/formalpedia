-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_seed_query_split
-- name    : ThreeSum.WeightedGlobalActualGlobalQueryRuntime.seed_query_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:59:58.835195+00:00
-- url     : https://prove2.me/theorems/eaab2d66-d19d-4704-b8e4-17de09ca6f2a
-- title:
--   Weighted Global Actual Global Query Runtime: seed query split
-- statement:
--   The Weighted Global Actual Global Query Runtime construction uses the seed query split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L80-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L80-L104

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualGlobalQueryRuntime
open Light Real Filter StageBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalActualColoredRuntime
open WeightedGlobalOversizePrime WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale WeightedGlobalEntropyRates
open scoped Topology BigOperators
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalActualGlobalQueryRuntime.seed_query_split {K k m F j seed : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : LightWeightedGlobalSeedScoreFactory.Data (config (nativePrime K m) j I A seed)) :
    LightWeightedGlobalSeedScoreFactory.runtime D
      (nativeHost (K:=K) (k:=k) j maps Q (sourceInput I A seed D)) K
      (4^fixedLength m) F (outputCap K k m F) ((nativePrime K m)*(nativePrime K m+1)^j)
      (WeightedGlobalGoodOutputCatalog.raws maps (threshold K k m))
      (WeightedGlobalGoodOutputCatalog.wordCodes maps (threshold K k m))
      (WeightedGlobalGoodOutputCatalog.mapCodes maps (threshold K k m))=
    LightWeightedGlobalSeedScoreFactory.runtime D
      (nativeHost (K:=K) (k:=k) j maps Q (sourceInput (zeroInput I) A seed D)) K
      (4^fixedLength m) F (outputCap K k m F) ((nativePrime K m)*(nativePrime K m+1)^j)
      (WeightedGlobalGoodOutputCatalog.raws maps (threshold K k m))
      (WeightedGlobalGoodOutputCatalog.wordCodes maps (threshold K k m))
      (WeightedGlobalGoodOutputCatalog.mapCodes maps (threshold K k m))+
      (A.J+2)^4*(nativeHost (K:=K) (k:=k) j maps Q (sourceInput I A seed D)).front.count*I.queryTime:= by sorry
