-- Prove2me | Theorems.Thm_ThreeSum_WeightedEnumeration_mem_words
-- name    : ThreeSum.WeightedEnumeration.mem_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:24:27.683093+00:00
-- url     : https://prove2.me/theorems/b1261f86-2629-44fe-8fac-77ba23e23d6c
-- title:
--   Weighted Enumeration: mem words
-- statement:
--   The Weighted Enumeration construction uses the mem words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Enumeration.lean#L39-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Enumeration.lean#L39-L77

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_Enumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedEnumeration.mem_words (n t : ℕ) (xs : List ℕ) :
    xs ∈ words n t ↔ xs.length = n ∧ (∀ d ∈ xs, d < 3) ∧ (xs.map digitCost).sum ≤ t := by sorry
