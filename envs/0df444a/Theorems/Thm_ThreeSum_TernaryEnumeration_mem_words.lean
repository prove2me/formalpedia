-- Prove2me | Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
-- name    : ThreeSum.TernaryEnumeration.mem_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:24:15.515748+00:00
-- url     : https://prove2.me/theorems/dff7a785-bff7-47e5-bd32-40b76e53c3b3
-- title:
--   Ternary Enumeration: mem words
-- statement:
--   The Ternary Enumeration construction uses the mem words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEnumeration.lean#L28-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEnumeration.lean#L28-L66

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryEnumeration

theorem ThreeSum.TernaryEnumeration.mem_words (n t : ℕ) (xs : List ℕ) :
    xs ∈ words n t ↔ xs.length = n ∧ (∀ d ∈ xs, d < 3) ∧ xs.sum ≤ t := by sorry
