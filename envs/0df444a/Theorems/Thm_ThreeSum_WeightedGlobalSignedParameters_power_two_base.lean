-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedParameters_power_two_base
-- name    : ThreeSum.WeightedGlobalSignedParameters.power_two_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:13:46.606062+00:00
-- url     : https://prove2.me/theorems/8340aef1-6db9-455f-b1af-7d777161ded9
-- title:
--   Weighted Global Signed Parameters: power two base
-- statement:
--   The Weighted Global Signed Parameters construction uses the power two base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedParameters.lean#L54-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedParameters.lean#L54-L71

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSignedParameters
open Filter Real WeightedGlobalSignedPadding WeightedGlobalCoverScale WeightedGlobalOversizeOverhead
open WeightedGlobalOversizePrime WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open WeightedGlobalOversizeRates WeightedGlobalParameters
open scoped Topology

theorem ThreeSum.WeightedGlobalSignedParameters.power_two_base {κ δ : ℝ} (hκ : 0≤κ) (hδ : 0<δ) :
    ∃ t : ℕ, 0<t ∧ 1<2^t ∧ κ*Real.log 2/Real.log ((2^t : ℕ) : ℝ)<δ/2 := by sorry
