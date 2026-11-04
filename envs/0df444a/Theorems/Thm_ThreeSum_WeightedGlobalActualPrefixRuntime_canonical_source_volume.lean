-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_canonical_source_volume
-- name    : ThreeSum.WeightedGlobalActualPrefixRuntime.canonical_source_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:06:00.313469+00:00
-- url     : https://prove2.me/theorems/94b93288-0529-4642-8b91-df6b9a648a69
-- title:
--   Weighted Global Actual Prefix Runtime: canonical source volume
-- statement:
--   All genuine canonical source dimensions fit the same four charged
--   volumes. In particular, source construction does not hide an N² join.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L375-L463
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L375-L463

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

theorem ThreeSum.WeightedGlobalActualPrefixRuntime.canonical_source_volume {K k b m n j F : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (I : Input) (right : Bool)
    (hK : 0<K) (hgood : GoodBlock K m) (hn : 1<n) (hb : 17≤b) (hFpos : 0<F)
    (hF : F≤(nativeFamily K m k).length)
    (hNL : (if right then I.nC else I.nB)≤n) :
    let cap:=WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)
    let S:=source (r:=j) maps cap I right
    (sourceVolume S.xs j ((nativePrime K m)^j) S.NL (nb m j) (F^j) ((F*cap)^j):ℝ)≤
      (F*endpointSize m+3:ℕ)*volumeBundle K k b m n j := by sorry
