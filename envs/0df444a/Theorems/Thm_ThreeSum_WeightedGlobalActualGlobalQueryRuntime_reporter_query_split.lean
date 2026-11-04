-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_reporter_query_split
-- name    : ThreeSum.WeightedGlobalActualGlobalQueryRuntime.reporter_query_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T00:04:16.115791+00:00
-- url     : https://prove2.me/theorems/de2adc5d-9458-4164-a979-15e4fcca3600
-- title:
--   Weighted Global Actual Global Query Runtime: reporter query split
-- statement:
--   The Weighted Global Actual Global Query Runtime construction uses the reporter query split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L199-L225
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L199-L225

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
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

theorem ThreeSum.WeightedGlobalActualGlobalQueryRuntime.reporter_query_split {K k m F j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (Hdet : ℕ) :
    let H:=nativeHost (K:=K) (k:=k) j maps Q I
    let Z:=nativeHost (K:=K) (k:=k) j maps Q (zeroInput I)
    LightWeightedGlobalMomentReporter.time H Hdet=LightWeightedGlobalMomentReporter.time Z Hdet+
      (TernaryMomentSchedule.channels (2*Hdet+1)).length*H.front.count*I.queryTime:= by sorry
