-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverFrequency_covers_raw_cap
-- name    : ThreeSum.WeightedGlobalCoverFrequency.covers_raw_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:58:10.866115+00:00
-- url     : https://prove2.me/theorems/d0965c4e-1fc4-4f7e-a91e-6d615a60c154
-- title:
--   Weighted Global Cover Frequency: covers raw cap
-- statement:
--   A positive retained hit certifies the full raw cap at every ordered
--   target pair, including pairs different from the one being covered.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverFrequency.lean#L139-L147
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverFrequency.lean#L139-L147

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_Weighted_Global_TernaryPartitionCount
import Definitions.Def_Submission_Weighted_Global_TernaryCoverFrequency
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverFrequency
open Finset TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]

theorem ThreeSum.WeightedGlobalCoverFrequency.covers_raw_cap {B τ : ℕ} {w : Weight m p} {t : ZMod p × ZMod p}
    (hc : Covers m p B τ w t) : rawCap (fixedAlpha m) (fixedPi m) w ≤ τ := by sorry
