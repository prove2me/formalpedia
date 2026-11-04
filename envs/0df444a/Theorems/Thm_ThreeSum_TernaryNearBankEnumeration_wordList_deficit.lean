-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_wordList_deficit
-- name    : ThreeSum.TernaryNearBankEnumeration.wordList_deficit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:38:05.693725+00:00
-- url     : https://prove2.me/theorems/a54598ad-bcae-4379-a385-4f824c13b112
-- title:
--   Ternary Near Bank Enumeration: word List deficit
-- statement:
--   The Ternary Near Bank Enumeration construction uses the word List deficit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearBankEnumeration.lean#L26-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearBankEnumeration.lean#L26-L35

import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration

theorem ThreeSum.TernaryNearBankEnumeration.wordList_deficit {N : ℕ} (Q R : TritWord N) :
    (List.zipWith Nat.sub (wordList Q) (wordList R)).sum = deficit Q R := by sorry
