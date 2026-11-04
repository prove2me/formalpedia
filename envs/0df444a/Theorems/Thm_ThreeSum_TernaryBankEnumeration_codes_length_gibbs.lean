-- Prove2me | Theorems.Thm_ThreeSum_TernaryBankEnumeration_codes_length_gibbs
-- name    : ThreeSum.TernaryBankEnumeration.codes_length_gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:36:08.839022+00:00
-- url     : https://prove2.me/theorems/ed58c8b1-c0f8-435c-8c35-995d27b49e99
-- title:
--   Ternary Bank Enumeration: codes length gibbs
-- statement:
--   The Ternary Bank Enumeration construction uses the codes length gibbs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L77-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L77-L80

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryBankEnumeration.codes_length_gibbs (N T : ℕ) (y : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    (codes N T).length * y ^ T ≤ (1 + y + y ^ 2) ^ N := by sorry
