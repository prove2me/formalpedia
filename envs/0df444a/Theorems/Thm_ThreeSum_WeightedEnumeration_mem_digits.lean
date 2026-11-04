-- Prove2me | Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
-- name    : ThreeSum.WeightedEnumeration.mem_digits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:24:24.955635+00:00
-- url     : https://prove2.me/theorems/46e55124-6cb7-42b1-b313-757a24a1fcbf
-- title:
--   Weighted Enumeration: mem digits
-- statement:
--   The Weighted Enumeration construction uses the mem digits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Enumeration.lean#L36-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Enumeration.lean#L36-L37

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_Enumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedEnumeration.mem_digits {d t : ℕ} : d ∈ digits t ↔ d < 3 ∧ digitCost d ≤ t := by sorry
