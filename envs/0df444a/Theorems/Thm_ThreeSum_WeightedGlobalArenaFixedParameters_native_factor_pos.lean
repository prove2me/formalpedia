-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_native_factor_pos
-- name    : ThreeSum.WeightedGlobalArenaFixedParameters.native_factor_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:14:34.268053+00:00
-- url     : https://prove2.me/theorems/891f8e36-53db-4892-9689-87813a273cc5
-- title:
--   Weighted Global Arena Fixed Parameters: native factor pos
-- statement:
--   The Weighted Global Arena Fixed Parameters construction uses the native factor pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFixedParameters.lean#L120-L121
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFixedParameters.lean#L120-L121

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

theorem ThreeSum.WeightedGlobalArenaFixedParameters.native_factor_pos {K : ℕ} (hK : 0<K) (m : ℕ) : 0<9*pairFactor m (familyLength K m) K := by sorry
