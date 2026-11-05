-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCountFrontendBudget_all_prefix_time_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCountFrontendBudget.all_prefix_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:22:02.72443+00:00
-- url     : https://prove2.me/theorems/48e3823d-3fd0-4d72-876a-5d939f84b1da
-- title:
--   all_prefix_time_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/CountFrontendBudget.lean#L327-L380
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/CountFrontendBudget.lean#L327-L380

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCountFrontendBudget.all_prefix_time_bound {K k m b C A degree : ℕ}
    (hK : 0<K) (hk : 0<k) (hm : 0<m) (c d : ℕ) (hb : b≤c*(fixedLength m+1)^d)
    (f g : ℕ→ℕ→Config) (groups wanted : ℕ→ℕ→ℕ) (channels : ℕ→ℕ)
    (hT : ∀ n, 1<n → ∀ j≤radixLength m n, (f n j).T=bankCut m j)
    (hgroups : ∀ n, 1<n → ∀ j≤radixLength m n, groups n j≤
      (b*(nativeFamily K m k).length*rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k)^j)
    (hwanted : ∀ n, 1<n → ∀ j≤radixLength m n, (wanted n j : ℝ)≤
      (n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j*
        ((b*(nativeFamily K m k).length*rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k : ℕ) : ℝ)^j)
    (hwidth : ∀ n, 1<n → ∀ j≤radixLength m n,
      width (fixedLength (j*m)) (f n j) (g n j)≤C*(radixLength m n+1))
    (hchannels : ∀ n, 1<n → channels n≤A*(radixLength m n+1)^degree)
    (n : ℕ) (hn : 1<n) :
    (allPrefixTime m f g groups wanted channels n : ℝ)≤
      ((A : ℝ)*dimensionConstant K k c d m*(C : ℝ)^3)*((radixLength m n : ℝ)+1)^(degree+4)*
        (n : ℝ)^principalExponent K k c d m := by sorry
