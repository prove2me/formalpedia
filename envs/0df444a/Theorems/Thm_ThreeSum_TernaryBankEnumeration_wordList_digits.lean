-- Prove2me | Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_digits
-- name    : ThreeSum.TernaryBankEnumeration.wordList_digits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:36:00.637077+00:00
-- url     : https://prove2.me/theorems/f6efab0b-93c9-4a67-8af0-5d031ad0d646
-- title:
--   Ternary Bank Enumeration: word List digits
-- statement:
--   The Ternary Bank Enumeration construction uses the word List digits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L21-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L21-L24

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryBankEnumeration.wordList_digits {N : ℕ} (w : TritWord N) : ∀ d ∈ wordList w, d < 3 := by sorry
