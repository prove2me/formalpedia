-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalSurvivors_mem_iff
-- name    : ThreeSum.LightOriginalSurvivors.mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:45:43.095447+00:00
-- url     : https://prove2.me/theorems/de108654-085d-4efc-8e27-d422959b6cf9
-- title:
--   Light Original Survivors: mem iff
-- statement:
--   The Light Original Survivors construction uses the mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivors.lean#L32-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivors.lean#L32-L39

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivors
open LightOriginalBucketFilter LightOriginalCollisionCleanup
attribute [local instance] Classical.propDecidable

theorem ThreeSum.LightOriginalSurvivors.mem_iff (keys : ℕ → ℕ) (n i : ℕ) :
    i ∈ indices keys n ↔ ∃ j < (indices keys n).length, index keys n j = i := by sorry
