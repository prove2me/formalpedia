-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeRates_native_rate_bounds
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeRates.native_rate_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:07:54.543464+00:00
-- url     : https://prove2.me/theorems/664ccbc6-7536-486d-92da-fd58bd844949
-- title:
--   native_rate_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryOversizeRates.lean#L67-L98
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryOversizeRates.lean#L67-L98

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeRates
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeRates
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime
open scoped Topology
set_option maxHeartbeats 1000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeRates.native_rate_bounds {K m : ℕ} (hK : 0 < K) (hm : 0 < m) :
    (outputRate m+partitionEntropy)/2+inflationRate K m ≤ nativeRate K m ∧
    nativeRate K m ≤ (outputRate m+partitionEntropy)/2+inflationRate K m+
      Real.log 16/(2*((fixedLength m : ℝ)*Real.log 2)) := by sorry
