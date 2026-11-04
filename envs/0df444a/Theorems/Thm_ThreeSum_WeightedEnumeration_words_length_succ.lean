-- Prove2me | Theorems.Thm_ThreeSum_WeightedEnumeration_words_length_succ
-- name    : ThreeSum.WeightedEnumeration.words_length_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:24:38.019741+00:00
-- url     : https://prove2.me/theorems/ad6e907a-c3f5-44c9-847f-ae3ef5ff2519
-- title:
--   Weighted Enumeration: words length succ
-- statement:
--   The Weighted Enumeration construction uses the words length succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Enumeration.lean#L100-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Enumeration.lean#L100-L103

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_Enumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedEnumeration.words_length_succ (n t : ℕ) :
    (words (n + 1) t).length =
      ((digits t).map fun d => (words n (t - digitCost d)).length).sum := by sorry
