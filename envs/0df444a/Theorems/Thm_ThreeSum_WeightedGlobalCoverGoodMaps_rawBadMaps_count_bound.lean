-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverGoodMaps_rawBadMaps_count_bound
-- name    : ThreeSum.WeightedGlobalCoverGoodMaps.rawBadMaps_count_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:57:58.997571+00:00
-- url     : https://prove2.me/theorems/ecd6d4ed-3af3-4e23-8ea9-504f4a320892
-- title:
--   Weighted Global Cover Good Maps: raw Bad Maps count bound
-- statement:
--   The Weighted Global Cover Good Maps construction uses the raw Bad Maps count bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverGoodMaps.lean#L38-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverGoodMaps.lean#L38-L46

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverActualMoment
import Definitions.Def_Submission_ThreeSum_Cover
import Definitions.Def_Submission_Weighted_Global_TernaryCoverGoodMaps
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverGoodMaps
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open WeightedGlobalLocalParameters WeightedGlobalCoverActualMoment TernaryCoverMoments
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]

theorem ThreeSum.WeightedGlobalCoverGoodMaps.rawBadMaps_count_bound (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card *
      (2 ^ (fixedPi m 1) * 3 ^ (fixedPi m 2)) ≤ p ^ 2) (k τ : ℕ) :
    τ ^ k * (rawBadMaps m p τ).card ≤ p ^ 2 * 3 ^ (4*k^2) * Fintype.card (Weight m p) := by sorry
