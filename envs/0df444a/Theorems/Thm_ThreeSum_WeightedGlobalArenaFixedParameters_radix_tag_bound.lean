-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_radix_tag_bound
-- name    : ThreeSum.WeightedGlobalArenaFixedParameters.radix_tag_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:07:06.28691+00:00
-- url     : https://prove2.me/theorems/b31bf6cc-5535-4ce1-9a81-f9e2dddf889e
-- title:
--   Weighted Global Arena Fixed Parameters: radix tag bound
-- statement:
--   The actual source/tag coefficient bound fits the fixed word radix;
--   this follows from the existing minor guard, without another parameter choice.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFixedParameters.lean#L153-L175
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFixedParameters.lean#L153-L175

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

theorem ThreeSum.WeightedGlobalArenaFixedParameters.radix_tag_bound {K m radix : ℕ} (hK : 0<K) (hb : 1≤radix)
    (hminor : (2*K).factorial*radix^(2*K)<nativePrime K m) :
    radix≤2*(4^fixedLength m)+1 := by sorry
