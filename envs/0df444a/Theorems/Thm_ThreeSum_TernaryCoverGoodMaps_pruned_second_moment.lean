-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverGoodMaps_pruned_second_moment
-- name    : ThreeSum.TernaryCoverGoodMaps.pruned_second_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:49:11.989442+00:00
-- url     : https://prove2.me/theorems/d199492b-ded7-4bc9-9be5-d8fdd9a7bb30
-- title:
--   Ternary Cover Good Maps: pruned second moment
-- statement:
--   The Ternary Cover Good Maps construction uses the pruned second moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverGoodMaps.lean#L94-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverGoodMaps.lean#L94-L101

import Definitions.Def_Submission_ThreeSum_TernaryCoverActualMoment
import Definitions.Def_Submission_ThreeSum_Cover
import Definitions.Def_Submission_ThreeSum_TernaryCoverGoodMaps
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverGoodMaps
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryLocalParameters TernaryCoverActualMoment TernaryCoverMoments
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]

theorem ThreeSum.TernaryCoverGoodMaps.pruned_second_moment (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card *
      (2 ^ (fixedPi m 1) * 3 ^ (fixedPi m 2)) ≤ p ^ 2)
    (B τ : ℕ) (a b : ZMod p) :
    (∑ w : Weight m p, prunedHit m p B τ w a b ^ 2) ≤
      3 ^ 16 * Fintype.card (Weight m p) := by sorry
