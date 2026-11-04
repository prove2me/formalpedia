-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_rootCeiling_lower
-- name    : ThreeSum.WeightedGlobalOversizePrime.rootCeiling_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:50:31.701781+00:00
-- url     : https://prove2.me/theorems/fb6c135c-fe46-40fd-b65c-55d4fd2861df
-- title:
--   Weighted Global Oversize Prime: root Ceiling lower
-- statement:
--   The Weighted Global Oversize Prime construction uses the root Ceiling lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L34-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L34-L35

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000
attribute [local semireducible] nativePrime

theorem ThreeSum.WeightedGlobalOversizePrime.rootCeiling_lower {K M : ℕ} (hK : 0 < K) (hM : 0 < M) :
    M ≤ rootCeiling K M^K := by sorry
