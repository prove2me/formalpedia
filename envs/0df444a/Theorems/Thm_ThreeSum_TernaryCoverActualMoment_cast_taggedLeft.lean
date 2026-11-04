-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverActualMoment_cast_taggedLeft
-- name    : ThreeSum.TernaryCoverActualMoment.cast_taggedLeft
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:52.498898+00:00
-- url     : https://prove2.me/theorems/1db8a599-9d9a-4d69-a6c8-09ff4ac776b4
-- title:
--   Ternary Cover Actual Moment: cast tagged Left
-- statement:
--   The Ternary Cover Actual Moment construction uses the cast tagged Left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverActualMoment.lean#L25-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverActualMoment.lean#L25-L30

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

theorem ThreeSum.TernaryCoverActualMoment.cast_taggedLeft {L p : ℕ} [Fact p.Prime] {α π : DigitType} (e : LocalEdge L α π) :
    castWord (K := ZMod p) (taggedLeft e) = leftVector (fieldLeft (p := p) e) := by sorry
