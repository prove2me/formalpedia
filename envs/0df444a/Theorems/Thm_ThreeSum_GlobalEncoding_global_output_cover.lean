-- Prove2me | Theorems.Thm_ThreeSum_GlobalEncoding_global_output_cover
-- name    : ThreeSum.GlobalEncoding.global_output_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:28.874561+00:00
-- url     : https://prove2.me/theorems/c3e8cdf4-4445-4881-8b3a-99d8ba2948a6
-- title:
--   Global Encoding: global output cover
-- statement:
--   For every integer target pair there is a retained representation whose
--   output belongs to the explicitly bounded occurrence/output product and
--   whose output key is the target difference modulo the global modulus.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L296-L304
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L296-L304

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

theorem ThreeSum.GlobalEncoding.global_output_cover {h : ℕ} (hh : 0 < h) (J : ℕ) (a b : ℤ) :
    ∃ xs ∈ representations h J a b, ∃ q : GlobalOutput h J,
      globalKey q = Radix.positionalHash (localPrime h) rawRight xs -
        Radix.positionalHash (localPrime h) rawLeft xs ∧
      globalModulus h J ∣ (b - a) - globalKey q := by sorry
