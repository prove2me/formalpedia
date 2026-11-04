-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_charged_query_product
-- name    : ThreeSum.WeightedGlobalActualGlobalQueryRuntime.charged_query_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:57:36.448808+00:00
-- url     : https://prove2.me/theorems/4a5ac51e-2d0c-438e-ad0f-2fc6e5bf4b14
-- title:
--   Weighted Global Actual Global Query Runtime: charged query product
-- statement:
--   The Weighted Global Actual Global Query Runtime construction uses the charged query product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L265-L293
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L265-L293

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

theorem ThreeSum.WeightedGlobalActualGlobalQueryRuntime.charged_query_product {K k b m F β κ n D E B : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (S : State K m) (H : Fits (k:=k) maps Q (zeroState S) β κ n D E B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hF : F≤(nativeFamily K m k).length) (hb : WeightedGlobalActualPrefixRuntime.localFactor m≤b)
    (hquery : (queryCap S n:ℝ)≤(WeightedGlobalUniformQueryTime.coefficient m D E κ:ℝ)*
      (S.arena.J+1:ℕ)^3*WeightedGlobalCountFrontendBudget.envelope m (radixLength m n))
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d) :
    ((wantedCap K k m F n S.arena.J*queryCap S n:ℕ):ℝ)≤
      (WeightedGlobalUniformQueryTime.coefficient m D E κ:ℝ)*volumeConstant K k c d m*
        (S.arena.J+1:ℕ)^3*(2:ℝ)^S.arena.J*(n:ℝ)^fullExponent K k c d m:= by sorry
