-- Prove2me | Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
-- name    : ThreeSum.TernaryEnumeration.mem_digits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:24:19.08912+00:00
-- url     : https://prove2.me/theorems/40b82f77-0626-4fa1-a6c4-d6c02afb904a
-- title:
--   Ternary Enumeration: mem digits
-- statement:
--   The Ternary Enumeration construction uses the mem digits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEnumeration.lean#L25-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEnumeration.lean#L25-L26

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryEnumeration

theorem ThreeSum.TernaryEnumeration.mem_digits {d t : ℕ} : d ∈ digits t ↔ d < 3 ∧ d ≤ t := by sorry
