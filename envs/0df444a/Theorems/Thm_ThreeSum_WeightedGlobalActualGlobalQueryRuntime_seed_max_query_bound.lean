-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_seed_max_query_bound
-- name    : ThreeSum.WeightedGlobalActualGlobalQueryRuntime.seed_max_query_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T00:02:03.362489+00:00
-- url     : https://prove2.me/theorems/e285c164-34b8-4b92-af5a-d5a86ac2a8a1
-- title:
--   Weighted Global Actual Global Query Runtime: seed max query bound
-- statement:
--   The Weighted Global Actual Global Query Runtime construction uses the seed max query bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L120-L142
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L120-L142

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

theorem ThreeSum.WeightedGlobalActualGlobalQueryRuntime.seed_max_query_bound {K k m F n j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (S : State K m) (hF : 0<F) (hj : j≤radixLength m n)
    (hrequest : (S.phase j).requesterCount≤n*2^S.arena.J) :
    prefixSeedTime (K:=K) (k:=k) maps Q (S.phase j) S.arena (S.seeds j)≤
      prefixSeedTime (K:=K) (k:=k) maps Q ((zeroState S).phase j) S.arena ((zeroState S).seeds j)+
        (S.arena.J+2)^4*wantedCap K k m F n S.arena.J*queryCap S n:= by sorry
