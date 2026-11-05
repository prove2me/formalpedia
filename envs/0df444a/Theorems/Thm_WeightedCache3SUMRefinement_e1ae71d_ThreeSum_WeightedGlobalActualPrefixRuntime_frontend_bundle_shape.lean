-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalActualPrefixRuntime_frontend_bundle_shape
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualPrefixRuntime.frontend_bundle_shape
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:39:05.392372+00:00
-- url     : https://prove2.me/theorems/8170ee70-7730-4da7-900f-fd8b5002403f
-- title:
--   frontend_bundle_shape
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L572-L608
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L572-L608

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHostBudget
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentReporterBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedControllerBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPreparationBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualPrefixRuntime
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualPrefixRuntime
open Light Real Filter Asymptotics
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend
open WeightedGlobalEntropyRates WeightedGlobalDimensionBounds WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
open scoped BigOperators Topology
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualPrefixRuntime.frontend_bundle_shape {K k b m n j groups count carries : ℕ}
    (hK : 0<K) (hm : 0<m) (hn : 1<n) (hfactor : 1≤nativeFactor K k b m)
    (hcarries : 1≤carries) (f g : LightWeightedNearPair.Config)
    (hT : f.T=bankCut m j)
    (hgroups : groups≤nativeFactor K k b m^j)
    (hcount : (count:ℝ)≤(carries:ℝ)*(n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^j*
      (nativeFactor K k b m:ℝ)^j) :
    ((LightWeightedCountFrontend.time groups (fixedLength (j*m)) f.L (bankSize m j) count
      (WeightedGlobalCountFrontendBudget.queryMax m j f g)+1000:ℕ):ℝ)≤
      1000000*(WeightedGlobalCountFrontendBudget.width (fixedLength (j*m)) f g:ℝ)^3*
        (carries:ℝ)*volumeBundle K k b m n j := by sorry
