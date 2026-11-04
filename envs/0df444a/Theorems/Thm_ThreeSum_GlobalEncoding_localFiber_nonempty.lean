-- Prove2me | Theorems.Thm_ThreeSum_GlobalEncoding_localFiber_nonempty
-- name    : ThreeSum.GlobalEncoding.localFiber_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:30.869342+00:00
-- url     : https://prove2.me/theorems/89b04456-6438-498a-9429-f30c9991a275
-- title:
--   Global Encoding: local Fiber nonempty
-- statement:
--   The Global Encoding construction uses the local Fiber nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L107-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L107-L120

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

theorem ThreeSum.GlobalEncoding.localFiber_nonempty {h : ℕ} (hh : 0 < h) (a b : ℤ) :
    (Radix.localFiber (localPrime h) rawLeft rawRight a b : Finset (RetainedChoice h)).Nonempty := by sorry
