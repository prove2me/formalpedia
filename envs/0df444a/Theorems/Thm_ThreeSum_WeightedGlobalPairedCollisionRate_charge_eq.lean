-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPairedCollisionRate_charge_eq
-- name    : ThreeSum.WeightedGlobalPairedCollisionRate.charge_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:41:12.103817+00:00
-- url     : https://prove2.me/theorems/a2433f2c-a847-42f6-9c0d-9de0b3c70388
-- title:
--   Weighted Global Paired Collision Rate: charge eq
-- statement:
--   The Weighted Global Paired Collision Rate construction uses the charge eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedCollisionRate.lean#L46-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedCollisionRate.lean#L46-L55

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

theorem ThreeSum.WeightedGlobalPairedCollisionRate.charge_eq {K m : ℕ} (hm : 0<m) :
    charge K m=2+2*Real.log (9/(nativePrime K m : ℝ))/Real.log (outputSize m : ℝ) := by sorry
