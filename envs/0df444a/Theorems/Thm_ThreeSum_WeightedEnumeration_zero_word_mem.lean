-- Prove2me | Theorems.Thm_ThreeSum_WeightedEnumeration_zero_word_mem
-- name    : ThreeSum.WeightedEnumeration.zero_word_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:24:34.341212+00:00
-- url     : https://prove2.me/theorems/80f8d654-7762-4c1e-be8f-4d864a8dafd6
-- title:
--   Weighted Enumeration: zero word mem
-- statement:
--   The Weighted Enumeration construction uses the zero word mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Enumeration.lean#L79-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Enumeration.lean#L79-L81

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_Enumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedEnumeration.zero_word_mem (n t : ℕ) : List.replicate n 0 ∈ words n t := by sorry
