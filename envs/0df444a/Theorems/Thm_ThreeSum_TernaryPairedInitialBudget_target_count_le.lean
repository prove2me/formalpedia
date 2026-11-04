-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedInitialBudget_target_count_le
-- name    : ThreeSum.TernaryPairedInitialBudget.target_count_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:09:24.808492+00:00
-- url     : https://prove2.me/theorems/e83a655f-0ea6-496e-be72-0c777a80ac40
-- title:
--   Ternary Paired Initial Budget: target count le
-- statement:
--   The Ternary Paired Initial Budget construction uses the target count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedInitialBudget.lean#L28-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedInitialBudget.lean#L28-L34

import Definitions.Def_Submission_ThreeSum_TernaryPairedInitial
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitialBudget
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedInitialBudget

theorem ThreeSum.TernaryPairedInitialBudget.target_count_le (K Λ b n carries targets : ℕ) (ht : targets≤n*carries) :
    targets*n^(2*K)*Λ^(2*K)*((2*K).factorial*b^(2*K))^2≤upper K Λ b n carries := by sorry
