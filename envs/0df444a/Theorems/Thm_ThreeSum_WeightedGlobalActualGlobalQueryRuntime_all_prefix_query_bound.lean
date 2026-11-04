-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_all_prefix_query_bound
-- name    : ThreeSum.WeightedGlobalActualGlobalQueryRuntime.all_prefix_query_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T00:00:32.765574+00:00
-- url     : https://prove2.me/theorems/0cb3a33b-af64-4615-a079-5b876c0c60a4
-- title:
--   Weighted Global Actual Global Query Runtime: all prefix query bound
-- statement:
--   The Weighted Global Actual Global Query Runtime construction uses the all prefix query bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L165-L188
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L165-L188

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

theorem ThreeSum.WeightedGlobalActualGlobalQueryRuntime.all_prefix_query_bound {K k m F n : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (S : State K m) (hF : 0<F)
    (hrequest : ∀j≤radixLength m n,(S.phase j).requesterCount≤n*2^S.arena.J) :
    allPrefixTime (K:=K) (k:=k) maps Q S.phase S.arena S.seeds n≤
      allPrefixTime (K:=K) (k:=k) maps Q (zeroState S).phase S.arena (zeroState S).seeds n+
        prefixCorrection k F S n:= by sorry
