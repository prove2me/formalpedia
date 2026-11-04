-- Prove2me | Theorems.Thm_ThreeSum_GlobalEncoding_localFiber_card_bound
-- name    : ThreeSum.GlobalEncoding.localFiber_card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:30.786232+00:00
-- url     : https://prove2.me/theorems/42815b6e-be80-400c-af1b-451ce97488b7
-- title:
--   Global Encoding: local Fiber card bound
-- statement:
--   The exact local cap counts map occurrences separately, including
--   repetitions in the chosen greedy schedule.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L154-L166
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L154-L166

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

theorem ThreeSum.GlobalEncoding.localFiber_card_bound (h : ℕ) (a b : ℤ) :
    (Radix.localFiber (localPrime h) rawLeft rawRight a b : Finset (RetainedChoice h)).card ≤
      scheduleSize h * localBucketCap h ^ 2 := by sorry
