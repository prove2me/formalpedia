-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalSurvivors_index_mem
-- name    : ThreeSum.LightOriginalSurvivors.index_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:44:41.581717+00:00
-- url     : https://prove2.me/theorems/693819f2-991a-4295-976b-c05db4d272a5
-- title:
--   Light Original Survivors: index mem
-- statement:
--   The Light Original Survivors construction uses the index mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivors.lean#L25-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivors.lean#L25-L27

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivors
open LightOriginalBucketFilter LightOriginalCollisionCleanup
attribute [local instance] Classical.propDecidable

theorem ThreeSum.LightOriginalSurvivors.index_mem {keys : ℕ → ℕ} {n j : ℕ} (hj : j < (indices keys n).length) :
    index keys n j ∈ indices keys n := by sorry
