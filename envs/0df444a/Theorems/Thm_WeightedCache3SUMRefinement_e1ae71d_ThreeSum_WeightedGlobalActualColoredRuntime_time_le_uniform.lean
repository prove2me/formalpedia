-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalActualColoredRuntime_time_le_uniform
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualColoredRuntime.time_le_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:55:00.408783+00:00
-- url     : https://prove2.me/theorems/e5ff12e0-2e9c-4054-841a-d70436aa0f74
-- title:
--   time_le_uniform
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L491-L542
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryActualColoredRuntime.lean#L491-L542

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualRuntimeParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualCleanupRuntime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualColoredRuntime
import Theorems.Thm_ThreeSum_LightPrimality_time_le_uniform

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualColoredRuntime
open Light Real Filter StageBounds ArithmeticStageBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalEntropyRates
open WeightedGlobalOversizePrime WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
open scoped Topology BigOperators
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualColoredRuntime.time_le_uniform {K k b m F β κ n D E B Hdet : ℕ}
    {maps : Fin F→Weight m (nativePrime K m)} {Q : WeightedGlobalGoodOutputCatalog.Output m}
    {S : State K m} (H : Fits (k:=k) maps Q S β κ n D E B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : WeightedGlobalActualPrefixRuntime.localFactor m≤b)
    (hposL : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d)
    (hcharge : fullExponent K k c d m≤WeightedGlobalCountFrontendBudget.frontendExponent) :
    time (k:=k) maps Q S E κ Hdet n≤uniformTime K k c d m F D E κ B Hdet β n:= by sorry
