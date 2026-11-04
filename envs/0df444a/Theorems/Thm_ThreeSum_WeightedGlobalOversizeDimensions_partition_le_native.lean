-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeDimensions_partition_le_native
-- name    : ThreeSum.WeightedGlobalOversizeDimensions.partition_le_native
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:08:01.642309+00:00
-- url     : https://prove2.me/theorems/243ed7fc-09d9-4bcf-8863-5f1de7a16441
-- title:
--   Weighted Global Oversize Dimensions: partition le native
-- statement:
--   The Weighted Global Oversize Dimensions construction uses the partition le native property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L39-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L39-L41

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalPrincipalDimensions WeightedGlobalDimensionBounds TernaryJointType

theorem ThreeSum.WeightedGlobalOversizeDimensions.partition_le_native {K : ℕ} (hK : 0 < K) (m : ℕ) : partitionCap m ≤ nativePrime K m := by sorry
