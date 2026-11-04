-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualColoredRuntime_Fits_reporter_bound
-- name    : ThreeSum.WeightedGlobalActualColoredRuntime.Fits.reporter_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:43:20.704048+00:00
-- url     : https://prove2.me/theorems/b332b670-ff6b-42a6-a034-3ae5f8553773
-- title:
--   Fits: reporter bound
-- statement:
--   The Fits construction uses the reporter bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L345-L380
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L345-L380

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualRuntimeParameters
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualCleanupRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualColoredRuntime
open Light Real Filter StageBounds ArithmeticStageBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalEntropyRates
open WeightedGlobalOversizePrime WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
open scoped Topology BigOperators
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalActualColoredRuntime.Fits.reporter_bound {K k b m F β κ n D E B Hdet : ℕ}
    {maps : Fin F→Weight m (nativePrime K m)} {Q : WeightedGlobalGoodOutputCatalog.Output m}
    {S : State K m} (H : Fits (k:=k) maps Q S β κ n D E B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : WeightedGlobalActualPrefixRuntime.localFactor m≤b)
    (hposL : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d) :
    let host:=nativeHost (K:=K) (k:=k) (radixLength m n) maps Q S.post
    (LightWeightedGlobalMomentReporter.time host Hdet:ℝ)≤
      reporterCoefficient K k c d m F D E κ B Hdet*(S.arena.J+1:ℕ)^4*(2:ℝ)^S.arena.J*
        (n:ℝ)^fullExponent K k c d m:= by sorry
