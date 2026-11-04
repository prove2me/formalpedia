-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalTupleWantedLookup_encode_digits
-- name    : ThreeSum.WeightedGlobalTupleWantedLookup.encode_digits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:59:21.384596+00:00
-- url     : https://prove2.me/theorems/32bdba98-71f3-4c6e-930f-72078ef9cb1a
-- title:
--   Weighted Global Tuple Wanted Lookup: encode digits
-- statement:
--   The Weighted Global Tuple Wanted Lookup construction uses the encode digits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleWantedLookup.lean#L15-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleWantedLookup.lean#L15-L23

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Definitions.Def_Submission_Weighted_Global_TernaryTupleWantedLookup
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTupleWantedLookup
open TernaryWantedLittleEndian
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalTupleWantedLookup.encode_digits (digits : List ℕ) (R : ℕ) (is : List ℕ) (code scale : ℕ) :
    encode digits R code scale is=code+scale*Nat.ofDigits R (is.map (fun i => digits.getD i 0)) := by sorry
