-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalSurvivors_keys_injective
-- name    : ThreeSum.LightOriginalSurvivors.keys_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:45:27.342228+00:00
-- url     : https://prove2.me/theorems/6ad2ff23-8f30-4529-9c16-42cf5dc8312e
-- title:
--   Light Original Survivors: keys injective
-- statement:
--   The Light Original Survivors construction uses the keys injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivors.lean#L47-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivors.lean#L47-L54

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivors
open LightOriginalBucketFilter LightOriginalCollisionCleanup
attribute [local instance] Classical.propDecidable

theorem ThreeSum.LightOriginalSurvivors.keys_injective {keys : ℕ → ℕ} {n i j : ℕ}
    (hi : i < (indices keys n).length) (hj : j < (indices keys n).length)
    (he : keys (index keys n i) = keys (index keys n j)) : i = j := by sorry
