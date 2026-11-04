-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_words_image_nearWords
-- name    : ThreeSum.TernaryNearBankEnumeration.words_image_nearWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:38:08.513009+00:00
-- url     : https://prove2.me/theorems/4b9ee037-244e-42d7-b5ac-3ff36d7b5f62
-- title:
--   Ternary Near Bank Enumeration: words image near Words
-- statement:
--   The Ternary Near Bank Enumeration construction uses the words image near Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearBankEnumeration.lean#L42-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearBankEnumeration.lean#L42-L60

import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration

theorem ThreeSum.TernaryNearBankEnumeration.words_image_nearWords {N : ℕ} (Q : TritWord N) (D : ℕ) :
    (TernaryNearEnumeration.words (wordList Q) D).toFinset =
      (nearWords Q D).image wordList := by sorry
