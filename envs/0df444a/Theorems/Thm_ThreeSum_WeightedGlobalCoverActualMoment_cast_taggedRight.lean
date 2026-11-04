-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverActualMoment_cast_taggedRight
-- name    : ThreeSum.WeightedGlobalCoverActualMoment.cast_taggedRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:57:54.982195+00:00
-- url     : https://prove2.me/theorems/f752aa3f-fdc3-4658-aeca-e624112cb5dc
-- title:
--   Weighted Global Cover Actual Moment: cast tagged Right
-- statement:
--   The Weighted Global Cover Actual Moment construction uses the cast tagged Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverActualMoment.lean#L39-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverActualMoment.lean#L39-L44

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

theorem ThreeSum.WeightedGlobalCoverActualMoment.cast_taggedRight {L p : ℕ} [Fact p.Prime] {α π : DigitType} (e : LocalEdge L α π) :
    castWord (K := ZMod p) (taggedRight e) = rightVector (fieldRight (p := p) e) := by sorry
