-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_time_query_bound
-- name    : ThreeSum.WeightedGlobalActualGlobalQueryRuntime.time_query_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T00:01:10.205283+00:00
-- url     : https://prove2.me/theorems/d40a0df3-e851-464c-ab31-4a55ee17aa62
-- title:
--   Weighted Global Actual Global Query Runtime: time query bound
-- statement:
--   The Weighted Global Actual Global Query Runtime construction uses the time query bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L245-L263
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L245-L263

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

theorem ThreeSum.WeightedGlobalActualGlobalQueryRuntime.time_query_bound {K k m F β κ n D E B Hdet : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (S : State K m) (hF : 0<F)
    (H : Fits (k:=k) maps Q (zeroState S) β κ n D E B) :
    WeightedGlobalActualColoredRuntime.time (k:=k) maps Q S E κ Hdet n≤
      WeightedGlobalActualColoredRuntime.time (k:=k) maps Q (zeroState S) E κ Hdet n+
        totalCorrection k F Hdet S n:= by sorry
