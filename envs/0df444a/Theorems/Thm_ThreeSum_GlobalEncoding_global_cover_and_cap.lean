-- Prove2me | Theorems.Thm_ThreeSum_GlobalEncoding_global_cover_and_cap
-- name    : ThreeSum.GlobalEncoding.global_cover_and_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:25.752248+00:00
-- url     : https://prove2.me/theorems/acfeffcd-8ee5-49bc-a709-fc1f9b5489d4
-- title:
--   Global Encoding: global cover and cap
-- statement:
--   Actual global coverage and multiplicity, with no probabilistic, graph,
--   prime, or local-cover assumptions.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L195-L202
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L195-L202

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

theorem ThreeSum.GlobalEncoding.global_cover_and_cap {h : ℕ} (hh : 0 < h) (J : ℕ) (a b : ℤ) :
    (∃ xs : List (RetainedChoice h), xs.length = J ∧
      globalModulus h J ∣ a - Radix.positionalHash (localPrime h) rawLeft xs ∧
      globalModulus h J ∣ b - Radix.positionalHash (localPrime h) rawRight xs) ∧
      (representations h J a b).card ≤ representationCap h J := by sorry
