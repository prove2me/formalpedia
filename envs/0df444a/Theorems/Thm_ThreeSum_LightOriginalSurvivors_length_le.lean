-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalSurvivors_length_le
-- name    : ThreeSum.LightOriginalSurvivors.length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:44:40.928751+00:00
-- url     : https://prove2.me/theorems/6a2f6750-34eb-4502-8e99-7fe010fe0ebb
-- title:
--   Light Original Survivors: length le
-- statement:
--   The Light Original Survivors construction uses the length le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivors.lean#L22-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivors.lean#L22-L23

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivors
open LightOriginalBucketFilter LightOriginalCollisionCleanup
attribute [local instance] Classical.propDecidable

theorem ThreeSum.LightOriginalSurvivors.length_le (keys : ℕ → ℕ) (n : ℕ) : (indices keys n).length ≤ n := by sorry
