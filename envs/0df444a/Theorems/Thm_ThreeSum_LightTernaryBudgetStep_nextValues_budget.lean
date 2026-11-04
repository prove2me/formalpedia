-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryBudgetStep_nextValues_budget
-- name    : ThreeSum.LightTernaryBudgetStep.nextValues_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:03:57.784863+00:00
-- url     : https://prove2.me/theorems/db29a2fe-e383-4d61-ba21-d9ac1999d7dd
-- title:
--   Light Ternary Budget Step: next Values budget
-- statement:
--   The Light Ternary Budget Step construction uses the next Values budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBudgetStep.lean#L98-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBudgetStep.lean#L98-L103

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryBudgetStep
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBudgetStep
open Light
set_option maxHeartbeats 3000000

theorem ThreeSum.LightTernaryBudgetStep.nextValues_budget (p a b s j N U : ℕ) :
    nextValues p a b s (p^j) (p^j) (a^j) (9^j*N) (9^j*N) (U*(b*s)^j)=
      oldValues (p^(j+1)) (p^(j+1)) (a^(j+1)) (9^(j+1)*N) (9^(j+1)*N) (U*(b*s)^(j+1)) := by sorry
