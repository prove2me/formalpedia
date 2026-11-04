-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverActualMoment_cast_taggedRight
-- name    : ThreeSum.TernaryCoverActualMoment.cast_taggedRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:42.263195+00:00
-- url     : https://prove2.me/theorems/0108e4be-443f-48ca-b055-31d7616dad63
-- title:
--   Ternary Cover Actual Moment: cast tagged Right
-- statement:
--   The Ternary Cover Actual Moment construction uses the cast tagged Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverActualMoment.lean#L32-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverActualMoment.lean#L32-L37

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

theorem ThreeSum.TernaryCoverActualMoment.cast_taggedRight {L p : ℕ} [Fact p.Prime] {α π : DigitType} (e : LocalEdge L α π) :
    castWord (K := ZMod p) (taggedRight e) = rightVector (fieldRight (p := p) e) := by sorry
