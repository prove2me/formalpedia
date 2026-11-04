-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualColoredRuntime_Fits_prefix_bound
-- name    : ThreeSum.WeightedGlobalActualColoredRuntime.Fits.prefix_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:47:10.792448+00:00
-- url     : https://prove2.me/theorems/20260624-144b-49f0-8efc-8780ec64775b
-- title:
--   Fits: prefix bound
-- statement:
--   The Fits construction uses the prefix bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L240-L262
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L240-L262

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

theorem ThreeSum.WeightedGlobalActualColoredRuntime.Fits.prefix_bound {K k b m F β κ n D E B : ℕ}
    {maps : Fin F→Weight m (nativePrime K m)} {Q : WeightedGlobalGoodOutputCatalog.Output m}
    {S : State K m} (H : Fits (k:=k) maps Q S β κ n D E B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : WeightedGlobalActualPrefixRuntime.localFactor m≤b)
    (hposL : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d) :
    (allPrefixTime (K:=K) (k:=k) maps Q S.phase S.arena S.seeds n:ℝ)≤
      prefixConstant K k c d m F D E κ B*(S.arena.J+1:ℕ)^(seedPolynomialD K (nativePrime K m) B+6)*
        (2:ℝ)^S.arena.J*(n:ℝ)^fullExponent K k c d m:= by sorry
