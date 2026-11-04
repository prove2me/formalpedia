-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedRecurrence_paired_fourth_power_bound
-- name    : ThreeSum.TernaryPairedRecurrence.paired_fourth_power_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:44.840061+00:00
-- url     : https://prove2.me/theorems/72593469-1dc7-44f1-8f48-03907d2cbc2c
-- title:
--   Ternary Paired Recurrence: paired fourth power bound
-- statement:
--   A fixed strict oversize margin pays the initial `n^(2K+1)` score,
--   all carries, and every logarithmic minor factor.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedRecurrence.lean#L48-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedRecurrence.lean#L48-L56

import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedRecurrence

theorem ThreeSum.TernaryPairedRecurrence.paired_fourth_power_bound (K M a b : ℕ) (ha : 0<a) (score : ℕ → ℕ)
    (hstep : ∀ j, a*score (j+1)≤b*score j)
    (hbudget : b^4*M^(4*K+3)≤a^4) (r : ℕ) :
    M^(r*(4*K+3))*(score r)^4≤(score 0)^4 := by sorry
