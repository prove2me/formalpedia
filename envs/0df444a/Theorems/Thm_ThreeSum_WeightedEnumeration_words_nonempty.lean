-- Prove2me | Theorems.Thm_ThreeSum_WeightedEnumeration_words_nonempty
-- name    : ThreeSum.WeightedEnumeration.words_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:24:36.172992+00:00
-- url     : https://prove2.me/theorems/10e26e28-7b27-4fa3-8e17-1ba63fb2121d
-- title:
--   Weighted Enumeration: words nonempty
-- statement:
--   The Weighted Enumeration construction uses the words nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Enumeration.lean#L83-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Enumeration.lean#L83-L84

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_Enumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedEnumeration.words_nonempty (n t : ℕ) : 0 < (words n t).length := by sorry
