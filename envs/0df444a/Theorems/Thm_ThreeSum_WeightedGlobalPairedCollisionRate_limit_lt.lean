-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPairedCollisionRate_limit_lt
-- name    : ThreeSum.WeightedGlobalPairedCollisionRate.limit_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:43:08.141221+00:00
-- url     : https://prove2.me/theorems/293024d6-1dd2-43e8-bdee-8f7c92f2a33f
-- title:
--   Weighted Global Paired Collision Rate: limit lt
-- statement:
--   The Weighted Global Paired Collision Rate construction uses the limit lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedCollisionRate.lean#L31-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedCollisionRate.lean#L31-L40

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPairedFamilyMargin
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPairedCollisionRate
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalOversizeRates WeightedGlobalOversizePrime
open WeightedGlobalCoverScale WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalPairedCollisionRate.limit_lt {K : ℕ} (hK : 0<K) :
    1-partitionEntropy/Hpi-2/(K : ℝ)<(7483/10000 : ℝ) := by sorry
