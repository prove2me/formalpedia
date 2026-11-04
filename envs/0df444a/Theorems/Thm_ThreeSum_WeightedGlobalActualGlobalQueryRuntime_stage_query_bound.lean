-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_stage_query_bound
-- name    : ThreeSum.WeightedGlobalActualGlobalQueryRuntime.stage_query_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T00:02:07.93919+00:00
-- url     : https://prove2.me/theorems/498c4010-ab89-460a-9b22-c81c42e7866f
-- title:
--   Weighted Global Actual Global Query Runtime: stage query bound
-- statement:
--   The Weighted Global Actual Global Query Runtime construction uses the stage query bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L150-L163
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L150-L163

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

theorem ThreeSum.WeightedGlobalActualGlobalQueryRuntime.stage_query_bound {K k m F n j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (S : State K m) (hF : 0<F) (hj : j≤radixLength m n)
    (hrequest : (S.phase j).requesterCount≤n*2^S.arena.J) :
    prefixStageTime (K:=K) (k:=k) maps Q (S.phase j) S.arena (S.seeds j)≤
      prefixStageTime (K:=K) (k:=k) maps Q ((zeroState S).phase j) S.arena ((zeroState S).seeds j)+
        (menuSize K m S.arena.J*menuSize K m S.arena.J+1)*(S.arena.J+2)^4*
          wantedCap K k m F n S.arena.J*queryCap S n:= by sorry
