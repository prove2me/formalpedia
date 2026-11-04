-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedRecurrence_zero_of_iterated_bound
-- name    : ThreeSum.TernaryPairedRecurrence.zero_of_iterated_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:00:33.611121+00:00
-- url     : https://prove2.me/theorems/ddcb28f0-56a8-4b11-a3da-88c22c63d379
-- title:
--   Ternary Paired Recurrence: zero of iterated bound
-- statement:
--   The Ternary Paired Recurrence construction uses the zero of iterated bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedRecurrence.lean#L22-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedRecurrence.lean#L22-L30

import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedRecurrence

theorem ThreeSum.TernaryPairedRecurrence.zero_of_iterated_bound (a b : ℕ) (score : ℕ → ℕ)
    (hstep : ∀ j, a*score (j+1) ≤ b*score j) (r : ℕ)
    (hsmall : b^r*score 0 < a^r) : score r=0 := by sorry
