-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_micro_four
-- name    : ThreeSum.WeightedGlobalArenaFixedParameters.micro_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:06:12.416272+00:00
-- url     : https://prove2.me/theorems/156dd9a4-a837-4509-88f9-13f7685af444
-- title:
--   Weighted Global Arena Fixed Parameters: micro four
-- statement:
--   The Weighted Global Arena Fixed Parameters construction uses the micro four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFixedParameters.lean#L63-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFixedParameters.lean#L63-L71

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCarryBudget
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_Submission_Weighted_Global_TernaryPairedNativeDrift
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFixedParameters
open Filter WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalOversizeOverhead WeightedGlobalSignedPadding WeightedGlobalArenaBudgetExistence
open WeightedGlobalPairedCollisionRate WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedGlobalArenaFixedParameters.micro_four {K : ℕ} (hK : 0<K) : 4*microAllowance K<1 := by sorry
