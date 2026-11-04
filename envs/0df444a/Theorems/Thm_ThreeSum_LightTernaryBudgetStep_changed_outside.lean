-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryBudgetStep_changed_outside
-- name    : ThreeSum.LightTernaryBudgetStep.changed_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:26:57.559792+00:00
-- url     : https://prove2.me/theorems/3f1d5105-1282-4308-bcb3-aa999efe04a3
-- title:
--   Light Ternary Budget Step: changed outside
-- statement:
--   The Light Ternary Budget Step construction uses the changed outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBudgetStep.lean#L87-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBudgetStep.lean#L87-L96

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryBudgetStep
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBudgetStep
open Light
set_option maxHeartbeats 3000000

theorem ThreeSum.LightTernaryBudgetStep.changed_outside (μ : ℕ→ ℤ) (base p a b s xB xC xP tB tC tP : ℕ) :
    SameOutside μ (changed μ base p a b s xB xC xP tB tC tP) base 6 := by sorry
