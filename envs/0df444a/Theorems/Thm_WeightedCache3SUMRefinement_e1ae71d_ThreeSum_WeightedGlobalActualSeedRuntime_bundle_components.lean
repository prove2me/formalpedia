-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalActualSeedRuntime_bundle_components
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualSeedRuntime.bundle_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:44:03.693199+00:00
-- url     : https://prove2.me/theorems/31895f44-e634-4621-a5f6-a1db59abeb54
-- title:
--   bundle_components
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L63-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L63-L95

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySeedCoefficientBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualSeedRuntime
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualSeedRuntime
open Real Light Filter
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalEntropyRates WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualSeedRuntime.bundle_components {K k b m n j : ℕ} (hK : 0<K) (hn : 1<n)
    (hfactor : 1≤nativeFactor K k b m) :
    (n:ℝ)≤volumeBundle K k b m n j ∧
    ((nativePrime K m)^j:ℝ)≤volumeBundle K k b m n j ∧
    (nativeFactor K k b m:ℝ)^j*(n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^j≤volumeBundle K k b m n j ∧
    1≤volumeBundle K k b m n j := by sorry
