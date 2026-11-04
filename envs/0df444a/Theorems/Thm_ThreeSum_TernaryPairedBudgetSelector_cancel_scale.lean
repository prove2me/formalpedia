-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedBudgetSelector_cancel_scale
-- name    : ThreeSum.TernaryPairedBudgetSelector.cancel_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:08:35.281949+00:00
-- url     : https://prove2.me/theorems/ade8cfd7-5eca-41eb-9d72-c866b4bd624e
-- title:
--   Ternary Paired Budget Selector: cancel scale
-- statement:
--   Cancellation used after the actual scan has checked its scaled score.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedBudgetSelector.lean#L63-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedBudgetSelector.lean#L63-L66

import Definitions.Def_Submission_ThreeSum_TernaryPairedSelector
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_ThreeSum_TernaryPairedBudgetSelector
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedBudgetSelector
open Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem ThreeSum.TernaryPairedBudgetSelector.cancel_scale (a b s value budget : ℕ) (hs : 0<s)
    (h : a*(s*value)≤s*b*budget) : a*value≤b*budget := by sorry
