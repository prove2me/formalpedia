-- Prove2me | Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_injective
-- name    : ThreeSum.TernaryBankEnumeration.wordList_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:35:57.45628+00:00
-- url     : https://prove2.me/theorems/9542507d-0333-4185-8139-6512fc592e35
-- title:
--   Ternary Bank Enumeration: word List injective
-- statement:
--   The Ternary Bank Enumeration construction uses the word List injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L26-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L26-L31

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryBankEnumeration.wordList_injective (N : ℕ) : Function.Injective (@wordList N) := by sorry
