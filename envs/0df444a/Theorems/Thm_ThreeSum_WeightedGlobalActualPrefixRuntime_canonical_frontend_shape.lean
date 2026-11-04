-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_canonical_frontend_shape
-- name    : ThreeSum.WeightedGlobalActualPrefixRuntime.canonical_frontend_shape
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:12:23.088804+00:00
-- url     : https://prove2.me/theorems/88389cb2-590b-4a5a-9534-4030d70d8c49
-- title:
--   Weighted Global Actual Prefix Runtime: canonical frontend shape
-- statement:
--   Canonical CountFrontend runtime uses the actual proof-only typed query
--   maximum from CountReady. The wanted count is derived from literal entries.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L702-L744
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L702-L744

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHostBudget
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryMomentReporterBudget
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedControllerBudget
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Definitions.Def_Submission_Weighted_Global_TernarySignedPreparationBudget
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualPrefixRuntime
open Light Real Filter Asymptotics
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend
open WeightedGlobalEntropyRates WeightedGlobalDimensionBounds WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
open scoped BigOperators Topology
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalActualPrefixRuntime.canonical_frontend_shape {K k b m n j F carries : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (I : Input)
    (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (hK : 0<K) (hgood : GoodBlock K m) (hn : 1<n)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : localFactor m≤b) (hcarries : 1≤carries)
    (hrequest : I.requesterCount≤n*carries)
    (htime : I.queryTime≤WeightedGlobalCountFrontendBudget.queryMax m j
      (nearConfig (m:=m) (r:=j) I false
        (valueCap (r:=j) maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) I))
      (nearConfig (m:=m) (r:=j) I true
        (valueCap (r:=j) maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) I))) :
    let τ:=WeightedGlobalCoverCapParameters.rawThreshold (nativePrime K m)
      (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) k
    let S:=front (r:=j) maps τ (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) Q I
    ((S.runtime+1000:ℕ):ℝ)≤
      1000000*(WeightedGlobalCountFrontendBudget.width (N m j) S.f S.g:ℝ)^3*
        (carries:ℝ)*volumeBundle K k b m n j := by sorry
