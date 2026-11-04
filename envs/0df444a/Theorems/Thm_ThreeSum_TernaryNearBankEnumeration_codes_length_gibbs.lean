-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_codes_length_gibbs
-- name    : ThreeSum.TernaryNearBankEnumeration.codes_length_gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:16:17.308374+00:00
-- url     : https://prove2.me/theorems/8b09aa0f-dcff-43d7-99a8-b6d04c6bc871
-- title:
--   Ternary Near Bank Enumeration: codes length gibbs
-- statement:
--   The Ternary Near Bank Enumeration construction uses the codes length gibbs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearBankEnumeration.lean#L74-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearBankEnumeration.lean#L74-L79

import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_codes_length_gibbs

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration

theorem ThreeSum.TernaryNearBankEnumeration.codes_length_gibbs {N : ℕ} (Q : TritWord N) (D : ℕ) (z : ℝ)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (TernaryNearEnumeration.codes (wordList Q) D).length*z^D ≤
      ∏ i : Fin N, (if Q i=0 then 1 else if Q i=1 then 1+z else 1+z+z^2) := by sorry
