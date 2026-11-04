-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverActualMoment_tagged_endpoint_injective
-- name    : ThreeSum.TernaryCoverActualMoment.tagged_endpoint_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:46.162806+00:00
-- url     : https://prove2.me/theorems/a2c0ccd1-9b67-4610-ab15-e8d709e7e823
-- title:
--   Ternary Cover Actual Moment: tagged endpoint injective
-- statement:
--   The Ternary Cover Actual Moment construction uses the tagged endpoint injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverActualMoment.lean#L39-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverActualMoment.lean#L39-L50

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

theorem ThreeSum.TernaryCoverActualMoment.tagged_endpoint_injective {L p : ℕ} [Fact p.Prime] (α π : DigitType) (hp : 2 < p) :
    Function.Injective (fun e : LocalEdge L α π =>
      (castWord (K := ZMod p) (taggedLeft e), castWord (K := ZMod p) (taggedRight e))) := by sorry
