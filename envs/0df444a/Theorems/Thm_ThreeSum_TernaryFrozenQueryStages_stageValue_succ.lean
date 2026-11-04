-- Prove2me | Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_succ
-- name    : ThreeSum.TernaryFrozenQueryStages.stageValue_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:42:35.853994+00:00
-- url     : https://prove2.me/theorems/72a29ea4-ae35-4178-a278-0e13e6680c2b
-- title:
--   Ternary Frozen Query Stages: stage Value succ
-- statement:
--   The Ternary Frozen Query Stages construction uses the stage Value succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryStages.lean#L35-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryStages.lean#L35-L39

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryFrozenQueryStages.stageValue_succ {N K : ℕ} (hK : K<N) (H : TritWord N→ℤ) (R : TritWord N) :
    stageValue (K+1) H R =
      inverseDigit (fun d => stageValue K H (Function.update R ⟨K,hK⟩ d)) (R ⟨K,hK⟩) := by sorry
