-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPairedCollisionRate_charge_tendsto
-- name    : ThreeSum.WeightedGlobalPairedCollisionRate.charge_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:43:22.117225+00:00
-- url     : https://prove2.me/theorems/5b5d193d-5850-4164-bc74-f1081da61fe8
-- title:
--   Weighted Global Paired Collision Rate: charge tendsto
-- statement:
--   The Weighted Global Paired Collision Rate construction uses the charge tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedCollisionRate.lean#L21-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedCollisionRate.lean#L21-L29

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

theorem ThreeSum.WeightedGlobalPairedCollisionRate.charge_tendsto {K : ℕ} (hK : 0<K) :
    Tendsto (charge K) atTop (𝓝 (1-partitionEntropy/Hpi-2/(K : ℝ))) := by sorry
