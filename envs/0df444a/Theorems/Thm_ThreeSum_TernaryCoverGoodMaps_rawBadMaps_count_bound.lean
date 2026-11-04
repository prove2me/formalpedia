-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverGoodMaps_rawBadMaps_count_bound
-- name    : ThreeSum.TernaryCoverGoodMaps.rawBadMaps_count_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:48:30.360092+00:00
-- url     : https://prove2.me/theorems/feab2d83-7e2a-41da-aa86-693778d3b39a
-- title:
--   Ternary Cover Good Maps: raw Bad Maps count bound
-- statement:
--   The Ternary Cover Good Maps construction uses the raw Bad Maps count bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverGoodMaps.lean#L31-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverGoodMaps.lean#L31-L39

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

theorem ThreeSum.TernaryCoverGoodMaps.rawBadMaps_count_bound (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card *
      (2 ^ (fixedPi m 1) * 3 ^ (fixedPi m 2)) ≤ p ^ 2) (k τ : ℕ) :
    τ ^ k * (rawBadMaps m p τ).card ≤ p ^ 2 * 3 ^ (4*k^2) * Fintype.card (Weight m p) := by sorry
