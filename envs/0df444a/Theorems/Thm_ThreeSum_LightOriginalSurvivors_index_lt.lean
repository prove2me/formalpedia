-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalSurvivors_index_lt
-- name    : ThreeSum.LightOriginalSurvivors.index_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:44:37.297925+00:00
-- url     : https://prove2.me/theorems/a99dd5f9-2305-4215-84fc-6a7f43c83cd5
-- title:
--   Light Original Survivors: index lt
-- statement:
--   The Light Original Survivors construction uses the index lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivors.lean#L29-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivors.lean#L29-L30

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivors
open LightOriginalBucketFilter LightOriginalCollisionCleanup
attribute [local instance] Classical.propDecidable

theorem ThreeSum.LightOriginalSurvivors.index_lt {keys : ℕ → ℕ} {n j : ℕ} (hj : j < (indices keys n).length) :
    index keys n j < n := by sorry
