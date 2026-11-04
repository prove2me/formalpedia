-- Prove2me | Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_fromList
-- name    : ThreeSum.TernaryBankEnumeration.wordList_fromList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:36:00.320349+00:00
-- url     : https://prove2.me/theorems/3fabd6fb-d6e2-486f-b377-cebc1656f965
-- title:
--   Ternary Bank Enumeration: word List from List
-- statement:
--   The Ternary Bank Enumeration construction uses the word List from List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L43-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L43-L48

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryBankEnumeration.wordList_fromList {N : ℕ} (xs : List ℕ) (hlen : xs.length = N)
    (hdigits : ∀ d ∈ xs, d < 3) : wordList (fromList xs hlen hdigits) = xs := by sorry
