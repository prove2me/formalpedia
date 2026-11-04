-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_wordList_admitted
-- name    : ThreeSum.TernaryNearBankEnumeration.wordList_admitted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:38:05.135562+00:00
-- url     : https://prove2.me/theorems/c9a416c6-ed94-4fb6-b4e2-64505bd3d051
-- title:
--   Ternary Near Bank Enumeration: word List admitted
-- statement:
--   The Ternary Near Bank Enumeration construction uses the word List admitted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearBankEnumeration.lean#L37-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearBankEnumeration.lean#L37-L40

import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration

theorem ThreeSum.TernaryNearBankEnumeration.wordList_admitted {N D : ℕ} (Q R : TritWord N) :
    TernaryNearEnumeration.Admitted (wordList Q) (wordList R) D ↔
      R ∈ nearWords Q D := by sorry
