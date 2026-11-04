-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalSurvivors_index_strict
-- name    : ThreeSum.LightOriginalSurvivors.index_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:44:40.719176+00:00
-- url     : https://prove2.me/theorems/b3559826-1930-4527-943c-05a568fb4135
-- title:
--   Light Original Survivors: index strict
-- statement:
--   The Light Original Survivors construction uses the index strict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivors.lean#L41-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivors.lean#L41-L45

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivors
open LightOriginalBucketFilter LightOriginalCollisionCleanup
attribute [local instance] Classical.propDecidable

theorem ThreeSum.LightOriginalSurvivors.index_strict {keys : ℕ → ℕ} {n i j : ℕ}
    (hi : i < j) (hj : j < (indices keys n).length) : index keys n i < index keys n j := by sorry
