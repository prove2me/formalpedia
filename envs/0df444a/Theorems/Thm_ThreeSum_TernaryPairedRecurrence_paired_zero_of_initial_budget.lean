-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedRecurrence_paired_zero_of_initial_budget
-- name    : ThreeSum.TernaryPairedRecurrence.paired_zero_of_initial_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:47.947941+00:00
-- url     : https://prove2.me/theorems/7ab82bb3-2f9d-444a-8b6a-9329978a09c9
-- title:
--   Ternary Paired Recurrence: paired zero of initial budget
-- statement:
--   The Ternary Paired Recurrence construction uses the paired zero of initial budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedRecurrence.lean#L58-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedRecurrence.lean#L58-L75

import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedRecurrence

theorem ThreeSum.TernaryPairedRecurrence.paired_zero_of_initial_budget (K M a b n C : ℕ) (ha : 0<a)
    (score : ℕ → ℕ) (hstep : ∀ j, a*score (j+1)≤b*score j)
    (hbudget : b^4*M^(4*K+3)≤a^4) (r : ℕ)
    (hcover : n^2≤M^r) (hinit : (score 0)^4≤C*n^(8*K+5)) (hn : C<n) :
    score r=0 := by sorry
