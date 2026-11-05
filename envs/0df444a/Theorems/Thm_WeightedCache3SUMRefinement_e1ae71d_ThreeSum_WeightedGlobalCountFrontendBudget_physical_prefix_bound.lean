-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCountFrontendBudget_physical_prefix_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCountFrontendBudget.physical_prefix_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:22:23.127354+00:00
-- url     : https://prove2.me/theorems/a159972a-3f8a-4705-b084-a604ac004839
-- title:
--   physical_prefix_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/CountFrontendBudget.lean#L226-L302
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/CountFrontendBudget.lean#L226-L302

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_CountFrontendBudget
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCountFrontendBudget
open Filter Real Asymptotics
open TernaryJointType WeightedGlobalBank WeightedGlobalParameters WeightedGlobalDimensionBounds
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverCapParameters
open WeightedGlobalOversizeOverhead WeightedGlobalOversizeDimensions WeightedGlobalPrincipalDimensions
open LightWeightedNearPair
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 16000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCountFrontendBudget.physical_prefix_bound {K k m n j groups count b : ℕ}
    (hK : 0<K) (hk : 0<k) (hm : 0<m) (hn : 1<n) (hj : j≤radixLength m n)
    (c d : ℕ) (hb : b≤c*(fixedLength m+1)^d)
    (f g : Config) (hT : f.T=bankCut m j)
    (hgroups : groups≤(b*(nativeFamily K m k).length*
      WeightedGlobalCoverCapParameters.rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k)^j)
    (hcount : (count : ℝ)≤(n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j*
      ((b*(nativeFamily K m k).length*
        WeightedGlobalCoverCapParameters.rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k : ℕ) : ℝ)^j) :
    (LightWeightedCountFrontend.time groups (fixedLength (j*m)) f.L (bankSize m j) count (queryMax m j f g)+1000 : ℕ)≤
      dimensionConstant K k c d m*(width (fixedLength (j*m)) f g : ℝ)^3*
        (n : ℝ)^principalExponent K k c d m := by sorry
