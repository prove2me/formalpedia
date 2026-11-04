-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_prepared_post_query_split
-- name    : ThreeSum.WeightedGlobalActualGlobalQueryRuntime.prepared_post_query_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:55:01.074388+00:00
-- url     : https://prove2.me/theorems/297c8de4-420e-45f5-85be-cb14e8a585ab
-- title:
--   Weighted Global Actual Global Query Runtime: prepared post query split
-- statement:
--   The Weighted Global Actual Global Query Runtime construction uses the prepared post query split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L227-L239
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L227-L239

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

theorem ThreeSum.WeightedGlobalActualGlobalQueryRuntime.prepared_post_query_split {K k m F j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (Hdet : ℕ) (L : LightOriginalSurvivorPair.Layout) (keysB keysC : ℕ→ℕ) :
    let H:=nativeHost (K:=K) (k:=k) j maps Q I
    let Z:=nativeHost (K:=K) (k:=k) j maps Q (zeroInput I)
    LightWeightedGlobalPreparedPostSelection.time H Hdet L keysB keysC=
      LightWeightedGlobalPreparedPostSelection.time Z Hdet L keysB keysC+
        (TernaryMomentSchedule.channels (2*Hdet+1)).length*H.front.count*I.queryTime:= by sorry
