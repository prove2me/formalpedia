-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_codes_length_gibbs
-- name    : ThreeSum.WeightedNearBankEnumeration.codes_length_gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:25.750647+00:00
-- url     : https://prove2.me/theorems/7b4ebf8d-9785-4d0c-b551-0069194983d5
-- title:
--   Weighted Near Bank Enumeration: codes length gibbs
-- statement:
--   The Weighted Near Bank Enumeration construction uses the codes length gibbs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearBankEnumeration.lean#L87-L98
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearBankEnumeration.lean#L87-L98

import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_BankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_codes_length_gibbs

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.WeightedBankEnumeration
open WeightedCache (Below)
open ThreeSum.WeightedEnumeration (digitCost)

theorem ThreeSum.WeightedNearBankEnumeration.codes_length_gibbs {N : ℕ} (Q : TritWord N) (D : ℕ) (z : ℝ)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (WeightedNearEnumeration.codes (wordList Q) D).length*z^D ≤
      ∏ i : Fin N, (if Q i=0 then 1 else if Q i=1 then 1+z^512 else 1+z^513+z^1025) := by sorry
