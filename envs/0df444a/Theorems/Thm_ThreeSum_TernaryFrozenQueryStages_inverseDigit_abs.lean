-- Prove2me | Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_inverseDigit_abs
-- name    : ThreeSum.TernaryFrozenQueryStages.inverseDigit_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:43.807781+00:00
-- url     : https://prove2.me/theorems/5f20a252-dbaf-44be-abda-256cb50253c5
-- title:
--   Ternary Frozen Query Stages: inverse Digit abs
-- statement:
--   The Ternary Frozen Query Stages construction uses the inverse Digit abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryStages.lean#L41-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryStages.lean#L41-L57

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryFrozenQueryStages.inverseDigit_abs (f : Fin 3→ℤ) (B : ℤ) (hf : ∀ d, |f d|≤B) (q : Fin 3) :
    |inverseDigit f q|≤4*B := by sorry
