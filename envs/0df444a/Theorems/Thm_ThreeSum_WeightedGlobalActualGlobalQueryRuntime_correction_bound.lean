-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_correction_bound
-- name    : ThreeSum.WeightedGlobalActualGlobalQueryRuntime.correction_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T00:00:25.91375+00:00
-- url     : https://prove2.me/theorems/0c300a1b-7de7-4dc3-ae28-8a6e381c494b
-- title:
--   Weighted Global Actual Global Query Runtime: correction bound
-- statement:
--   The Weighted Global Actual Global Query Runtime construction uses the correction bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L320-L355
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean#L320-L355

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

theorem ThreeSum.WeightedGlobalActualGlobalQueryRuntime.correction_bound {K k b m F β κ n D E B Hdet : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (S : State K m) (H : Fits (k:=k) maps Q (zeroState S) β κ n D E B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hF : F≤(nativeFamily K m k).length) (hb : WeightedGlobalActualPrefixRuntime.localFactor m≤b)
    (hquery : (queryCap S n:ℝ)≤(WeightedGlobalUniformQueryTime.coefficient m D E κ:ℝ)*
      (S.arena.J+1:ℕ)^3*WeightedGlobalCountFrontendBudget.envelope m (radixLength m n))
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d)
    (hcharge : fullExponent K k c d m≤WeightedGlobalCountFrontendBudget.frontendExponent) :
    (totalCorrection k F Hdet S n:ℝ)≤
      extraCoefficient K k c d m F D E κ B Hdet*(J m β κ n+1:ℕ)^10*
        (2:ℝ)^J m β κ n*(n:ℝ)^WeightedGlobalCountFrontendBudget.frontendExponent:= by sorry
