-- Prove2me | Theorems.Thm_ThreeSum_TernaryEnumeration_words_length_succ
-- name    : ThreeSum.TernaryEnumeration.words_length_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:24:17.947088+00:00
-- url     : https://prove2.me/theorems/773468f3-3234-4eeb-821f-4b2af6130643
-- title:
--   Ternary Enumeration: words length succ
-- statement:
--   The Ternary Enumeration construction uses the words length succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEnumeration.lean#L89-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEnumeration.lean#L89-L92

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryEnumeration

theorem ThreeSum.TernaryEnumeration.words_length_succ (n t : ℕ) :
    (words (n + 1) t).length =
      ((digits t).map fun d => (words n (t - d)).length).sum := by sorry
