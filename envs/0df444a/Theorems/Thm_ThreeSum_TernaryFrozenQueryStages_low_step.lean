-- Prove2me | Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_low_step
-- name    : ThreeSum.TernaryFrozenQueryStages.low_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:42:18.522449+00:00
-- url     : https://prove2.me/theorems/baadf11a-88c4-4204-8c0b-bb7402275746
-- title:
--   Ternary Frozen Query Stages: low step
-- statement:
--   The Ternary Frozen Query Stages construction uses the low step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryStages.lean#L73-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryStages.lean#L73-L78

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryFrozenQueryStages.low_step {N K : ℕ} (hK : K<N) :
    TernaryCodeSemantics.low (⟨K,hK⟩ : Fin N)=2*(N-(K+1)) := by sorry
