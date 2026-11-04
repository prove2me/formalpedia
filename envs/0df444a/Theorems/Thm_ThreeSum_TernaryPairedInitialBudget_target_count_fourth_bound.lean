-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedInitialBudget_target_count_fourth_bound
-- name    : ThreeSum.TernaryPairedInitialBudget.target_count_fourth_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:22:33.572834+00:00
-- url     : https://prove2.me/theorems/86be1e75-b074-42e8-aea1-20f384b5fefe
-- title:
--   Ternary Paired Initial Budget: target count fourth bound
-- statement:
--   The Ternary Paired Initial Budget construction uses the target count fourth bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedInitialBudget.lean#L36-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedInitialBudget.lean#L36-L41

import Definitions.Def_Submission_ThreeSum_TernaryPairedInitial
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitialBudget
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedInitialBudget

theorem ThreeSum.TernaryPairedInitialBudget.target_count_fourth_bound (K Λ b n carries targets C : ℕ)
    (ht : targets≤n*carries) (hcarry : carries^4*Λ^(8*K)≤C*n) :
    (targets*n^(2*K)*Λ^(2*K)*((2*K).factorial*b^(2*K))^2)^4≤
      (C*((2*K).factorial*b^(2*K))^8)*n^(8*K+5) := by sorry
