-- Prove2me | Theorems.Thm_ThreeSum_GlobalEncoding_positionalHash_difference
-- name    : ThreeSum.GlobalEncoding.positionalHash_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:12:56.402318+00:00
-- url     : https://prove2.me/theorems/5e2adedc-32af-4e2e-b649-5016b77b3550
-- title:
--   Global Encoding: positional Hash difference
-- statement:
--   The Global Encoding construction uses the positional Hash difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L249-L258
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L249-L258

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments

theorem ThreeSum.GlobalEncoding.positionalHash_difference {h : ℕ} (xs : List (RetainedChoice h)) :
    Radix.positionalHash (localPrime h) rawRight xs -
      Radix.positionalHash (localPrime h) rawLeft xs =
        Radix.positionalHash (localPrime h) blockKey (xs.map blockOfChoice) := by sorry
