-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedBudgetSelector_terminal_fourth_bound
-- name    : ThreeSum.TernaryPairedBudgetSelector.terminal_fourth_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:08:38.150076+00:00
-- url     : https://prove2.me/theorems/63835e5c-289d-494d-b62d-952a1ab13b56
-- title:
--   Ternary Paired Budget Selector: terminal fourth bound
-- statement:
--   A single weighted budget at the final depth suffices; no evaluation
--   of Pi0 and no per-step comparison with its exact value is required.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedBudgetSelector.lean#L70-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedBudgetSelector.lean#L70-L89

import Definitions.Def_Submission_ThreeSum_TernaryPairedSelector
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_ThreeSum_TernaryPairedBudgetSelector
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedBudgetSelector
open Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem ThreeSum.TernaryPairedBudgetSelector.terminal_fourth_bound (K M a b U value r : ℕ) (hb : 0<b)
    (hbudget : a^r*value≤b^r*U) (hdrift : b^4*M^(4*K+3)≤a^4) :
    M^(r*(4*K+3))*value^4≤U^4 := by sorry
