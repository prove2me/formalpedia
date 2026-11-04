-- Prove2me | Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
-- name    : ThreeSum.TernaryBankEnumeration.wordList_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:35:59.025268+00:00
-- url     : https://prove2.me/theorems/42be31cf-6828-488f-8019-44396693404a
-- title:
--   Ternary Bank Enumeration: word List sum
-- statement:
--   The Ternary Bank Enumeration construction uses the word List sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L18-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L18-L19

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryBankEnumeration.wordList_sum {N : ℕ} (w : TritWord N) : (wordList w).sum = rank w := by sorry
