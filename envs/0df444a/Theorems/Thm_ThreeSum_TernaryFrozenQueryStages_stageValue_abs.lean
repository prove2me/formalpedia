-- Prove2me | Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_abs
-- name    : ThreeSum.TernaryFrozenQueryStages.stageValue_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:41:21.121674+00:00
-- url     : https://prove2.me/theorems/a9945e7f-8301-4294-b18a-7bb66ad6b6e1
-- title:
--   Ternary Frozen Query Stages: stage Value abs
-- statement:
--   The Ternary Frozen Query Stages construction uses the stage Value abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryStages.lean#L59-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryStages.lean#L59-L71

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryFrozenQueryStages.stageValue_abs {N : ℕ} (K : ℕ) (hK : K≤N) (H : TritWord N→ℤ) (U : ℕ)
    (hH : ∀ R, |H R|≤(U : ℤ)) (R : TritWord N) :
    |stageValue K H R|≤((4^K : ℕ) : ℤ)*(U : ℤ) := by sorry
