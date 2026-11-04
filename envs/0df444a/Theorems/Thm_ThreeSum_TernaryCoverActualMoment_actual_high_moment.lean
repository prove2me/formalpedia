-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverActualMoment_actual_high_moment
-- name    : ThreeSum.TernaryCoverActualMoment.actual_high_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:17:30.351969+00:00
-- url     : https://prove2.me/theorems/4a0ce89b-e1d4-4592-9ea6-e5c399806163
-- title:
--   Ternary Cover Actual Moment: actual high moment
-- statement:
--   The Ternary Cover Actual Moment construction uses the actual high moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverActualMoment.lean#L59-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverActualMoment.lean#L59-L89

import Definitions.Def_Submission_ThreeSum_TernaryCoverHighMoment
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverActualMoment
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverActualMoment
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryCoverHighMoment TernaryCoverRankFibers TernaryLocalParameters
open TernaryCoverOutputCap
open scoped BigOperators

theorem ThreeSum.TernaryCoverActualMoment.actual_high_moment (m p : ℕ) [Fact p.Prime] (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card *
      (2 ^ (fixedPi m 1) * 3 ^ (fixedPi m 2)) ≤ p ^ 2)
    (k : ℕ) (a b : ZMod p) :
    (∑ w : Coordinate (Fin (fixedLength m)) → ZMod p,
      TernaryCoverFibers.rawPairCount
        (leftHash (α := fixedAlpha m) (π := fixedPi m) w) (rightHash w) a b ^ k) ≤
      3 ^ (4*k^2) * Fintype.card (Coordinate (Fin (fixedLength m)) → ZMod p) := by sorry
