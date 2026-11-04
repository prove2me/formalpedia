-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_visits_le_nearWords
-- name    : ThreeSum.TernaryNearBankEnumeration.visits_le_nearWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:38:14.453291+00:00
-- url     : https://prove2.me/theorems/1ff8af37-65d7-45e6-be76-0c81fb9a69f3
-- title:
--   Ternary Near Bank Enumeration: visits le near Words
-- statement:
--   The Ternary Near Bank Enumeration construction uses the visits le near Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearBankEnumeration.lean#L69-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearBankEnumeration.lean#L69-L72

import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration

theorem ThreeSum.TernaryNearBankEnumeration.visits_le_nearWords {N : ℕ} (Q : TritWord N) (D : ℕ) :
    TernaryNearEnumeration.visits (wordList Q) D ≤ (N+1)*(nearWords Q D).card := by sorry
