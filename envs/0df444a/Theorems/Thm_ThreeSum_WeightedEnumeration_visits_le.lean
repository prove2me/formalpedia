-- Prove2me | Theorems.Thm_ThreeSum_WeightedEnumeration_visits_le
-- name    : ThreeSum.WeightedEnumeration.visits_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:25:23.267413+00:00
-- url     : https://prove2.me/theorems/8e47ad87-8ac2-4c5d-85b4-2aeb252cc775
-- title:
--   Weighted Enumeration: visits le
-- statement:
--   The Weighted Enumeration construction uses the visits le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Enumeration.lean#L105-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Enumeration.lean#L105-L116

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_Enumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedEnumeration.visits_le (n t : ℕ) : visits n t ≤ (n + 1) * (words n t).length := by sorry
