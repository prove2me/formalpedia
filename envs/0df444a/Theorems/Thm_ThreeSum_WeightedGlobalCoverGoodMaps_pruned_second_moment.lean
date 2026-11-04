-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverGoodMaps_pruned_second_moment
-- name    : ThreeSum.WeightedGlobalCoverGoodMaps.pruned_second_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:57:53.021248+00:00
-- url     : https://prove2.me/theorems/83dcc3f7-aad3-4b7a-b2d0-b40294ba3d84
-- title:
--   Weighted Global Cover Good Maps: pruned second moment
-- statement:
--   The Weighted Global Cover Good Maps construction uses the pruned second moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverGoodMaps.lean#L101-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverGoodMaps.lean#L101-L108

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

theorem ThreeSum.WeightedGlobalCoverGoodMaps.pruned_second_moment (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card *
      (2 ^ (fixedPi m 1) * 3 ^ (fixedPi m 2)) ≤ p ^ 2)
    (B τ : ℕ) (a b : ZMod p) :
    (∑ w : Weight m p, prunedHit m p B τ w a b ^ 2) ≤
      3 ^ 16 * Fintype.card (Weight m p) := by sorry
