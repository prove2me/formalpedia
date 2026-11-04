-- Prove2me | Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_high_step
-- name    : ThreeSum.TernaryFrozenQueryStages.high_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:42:27.261915+00:00
-- url     : https://prove2.me/theorems/87d7fa80-369e-4afc-b9dc-fd94687d4344
-- title:
--   Ternary Frozen Query Stages: high step
-- statement:
--   The Ternary Frozen Query Stages construction uses the high step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryStages.lean#L80-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryStages.lean#L80-L82

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryFrozenQueryStages.high_step {N K : ℕ} (hK : K<N) :
    TernaryCodeSemantics.high (⟨K,hK⟩ : Fin N)=2*(N-(K+1))+1 := by sorry
