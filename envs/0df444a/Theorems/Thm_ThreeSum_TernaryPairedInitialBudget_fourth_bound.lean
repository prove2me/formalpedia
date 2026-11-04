-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedInitialBudget_fourth_bound
-- name    : ThreeSum.TernaryPairedInitialBudget.fourth_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:08:43.699996+00:00
-- url     : https://prove2.me/theorems/a123eeb8-5552-4237-b64b-89a408fbf0a3
-- title:
--   Ternary Paired Initial Budget: fourth bound
-- statement:
--   The Ternary Paired Initial Budget construction uses the fourth bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedInitialBudget.lean#L9-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedInitialBudget.lean#L9-L25

import Definitions.Def_Submission_ThreeSum_TernaryPairedInitial
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitialBudget
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedInitialBudget

theorem ThreeSum.TernaryPairedInitialBudget.fourth_bound (K Λ b n carries C : ℕ)
    (hcarry : carries^4*Λ^(8*K)≤C*n) :
    (upper K Λ b n carries)^4≤
      (C*((2*K).factorial*b^(2*K))^8)*n^(8*K+5) := by sorry
