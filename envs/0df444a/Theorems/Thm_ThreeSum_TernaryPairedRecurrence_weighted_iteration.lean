-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedRecurrence_weighted_iteration
-- name    : ThreeSum.TernaryPairedRecurrence.weighted_iteration
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:47.119837+00:00
-- url     : https://prove2.me/theorems/7e13f82d-456f-4734-aaa0-33441d9141c3
-- title:
--   Ternary Paired Recurrence: weighted iteration
-- statement:
--   The Ternary Paired Recurrence construction uses the weighted iteration property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedRecurrence.lean#L32-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedRecurrence.lean#L32-L44

import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedRecurrence

theorem ThreeSum.TernaryPairedRecurrence.weighted_iteration (a b c : ℕ) (ha : 0<a) (score : ℕ → ℕ)
    (hstep : ∀ j, a*score (j+1)≤b*score j) (hbudget : b*c≤a) (r : ℕ) :
    c^r*score r≤score 0 := by sorry
