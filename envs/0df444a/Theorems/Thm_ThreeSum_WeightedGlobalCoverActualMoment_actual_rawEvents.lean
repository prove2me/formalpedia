-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverActualMoment_actual_rawEvents
-- name    : ThreeSum.WeightedGlobalCoverActualMoment.actual_rawEvents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:01.070193+00:00
-- url     : https://prove2.me/theorems/cb42f218-4fc1-4cae-9546-10eee0b71b75
-- title:
--   Weighted Global Cover Actual Moment: actual raw Events
-- statement:
--   The Weighted Global Cover Actual Moment construction uses the actual raw Events property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverActualMoment.lean#L59-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverActualMoment.lean#L59-L64

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryCoverHighMoment
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_Submission_Weighted_Global_TernaryCoverActualMoment
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverActualMoment
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryCoverHighMoment TernaryCoverRankFibers WeightedGlobalLocalParameters
open TernaryCoverOutputCap
open scoped BigOperators

theorem ThreeSum.WeightedGlobalCoverActualMoment.actual_rawEvents {L p : ℕ} [Fact p.Prime] (α π : DigitType) (a b : ZMod p) :
    rawEvents (fun e : LocalEdge L α π => taggedLeft e) taggedRight a b =
      (fun e => pairEvent (fieldLeft (p := p) e) (fieldRight e) a b) := by sorry
