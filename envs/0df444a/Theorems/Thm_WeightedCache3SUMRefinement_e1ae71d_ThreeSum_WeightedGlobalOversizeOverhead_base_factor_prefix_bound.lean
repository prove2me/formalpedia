-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeOverhead_base_factor_prefix_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeOverhead.base_factor_prefix_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:14:07.916723+00:00
-- url     : https://prove2.me/theorems/1bef5bf3-7aca-45bc-9705-ba34d9c073df
-- title:
--   base_factor_prefix_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L217-L241
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L217-L241

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeRates
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeOverhead
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeOverhead
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
open scoped Topology
set_option maxHeartbeats 1000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeOverhead.base_factor_prefix_bound {K k m n j : ℕ} (hK : 0 < K) (hk : 0 < k)
    (hm : 0 < m) (hn : 1 < n) (hj : j ≤ radixLength m n) (c d : ℕ) :
    (baseFactor K k c d m : ℝ)^j ≤ (baseFactor K k c d m : ℝ)*(n : ℝ)^overheadCharge k c d m := by sorry
