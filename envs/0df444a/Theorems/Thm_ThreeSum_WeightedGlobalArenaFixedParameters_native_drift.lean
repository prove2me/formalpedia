-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_native_drift
-- name    : ThreeSum.WeightedGlobalArenaFixedParameters.native_drift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:15:31.140324+00:00
-- url     : https://prove2.me/theorems/82b8e928-bae4-4bd3-aae8-f6e4399068cf
-- title:
--   Weighted Global Arena Fixed Parameters: native drift
-- statement:
--   The Weighted Global Arena Fixed Parameters construction uses the native drift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFixedParameters.lean#L26-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFixedParameters.lean#L26-L33

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

theorem ThreeSum.WeightedGlobalArenaFixedParameters.native_drift {K m F : ℕ} (hK : 0<K) (hF : (9*F)^4≤outputSize m) :
    (9*pairFactor m F K)^4*(outputSize m)^(4*K+3)≤((nativePrime K m)^(2*K))^4 := by sorry
