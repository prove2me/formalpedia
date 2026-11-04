-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverActualMoment_tagged_endpoint_injective
-- name    : ThreeSum.WeightedGlobalCoverActualMoment.tagged_endpoint_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:57:54.602787+00:00
-- url     : https://prove2.me/theorems/4883beb4-977b-43ef-b7b6-a4ed829c4a7f
-- title:
--   Weighted Global Cover Actual Moment: tagged endpoint injective
-- statement:
--   The Weighted Global Cover Actual Moment construction uses the tagged endpoint injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverActualMoment.lean#L46-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverActualMoment.lean#L46-L57

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

theorem ThreeSum.WeightedGlobalCoverActualMoment.tagged_endpoint_injective {L p : ℕ} [Fact p.Prime] (α π : DigitType) (hp : 2 < p) :
    Function.Injective (fun e : LocalEdge L α π =>
      (castWord (K := ZMod p) (taggedLeft e), castWord (K := ZMod p) (taggedRight e))) := by sorry
