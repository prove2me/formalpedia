-- Prove2me | Theorems.Thm_ThreeSum_TernaryHybridCosts_fastTime_powerBound
-- name    : ThreeSum.TernaryHybridCosts.fastTime_powerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:44:52.244521+00:00
-- url     : https://prove2.me/theorems/08ecddee-97e4-49c8-b0f2-c086fe9e66c2
-- title:
--   Ternary Hybrid Costs: fast Time power Bound
-- statement:
--   The Ternary Hybrid Costs construction uses the fast Time power Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridCosts.lean#L27-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridCosts.lean#L27-L32

import Definitions.Def_Submission_ThreeSum_TernaryHybridCore
import Definitions.Def_Submission_ThreeSum_TernaryEndBridge
import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridCosts
open Light StageBounds Filter
noncomputable section

theorem ThreeSum.TernaryHybridCosts.fastTime_powerBound {T : ℕ → ℕ} {a : ℝ}
    (hT : PowerBound T a) (ha : 0 ≤ a) (κ : ℕ) :
    PowerBound (fastTime T κ) a := by sorry
