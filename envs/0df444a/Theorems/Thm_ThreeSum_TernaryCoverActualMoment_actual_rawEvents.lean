-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverActualMoment_actual_rawEvents
-- name    : ThreeSum.TernaryCoverActualMoment.actual_rawEvents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:48.536606+00:00
-- url     : https://prove2.me/theorems/2cd13c53-31db-4f4b-ba60-39e5355b4490
-- title:
--   Ternary Cover Actual Moment: actual raw Events
-- statement:
--   The Ternary Cover Actual Moment construction uses the actual raw Events property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverActualMoment.lean#L52-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverActualMoment.lean#L52-L57

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

theorem ThreeSum.TernaryCoverActualMoment.actual_rawEvents {L p : ℕ} [Fact p.Prime] (α π : DigitType) (a b : ZMod p) :
    rawEvents (fun e : LocalEdge L α π => taggedLeft e) taggedRight a b =
      (fun e => pairEvent (fieldLeft (p := p) e) (fieldRight e) a b) := by sorry
