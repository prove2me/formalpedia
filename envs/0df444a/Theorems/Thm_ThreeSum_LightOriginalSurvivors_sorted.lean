-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalSurvivors_sorted
-- name    : ThreeSum.LightOriginalSurvivors.sorted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:44:49.728218+00:00
-- url     : https://prove2.me/theorems/69741a84-8782-4606-bf7c-fab637bc0f03
-- title:
--   Light Original Survivors: sorted
-- statement:
--   The Light Original Survivors construction uses the sorted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivors.lean#L56-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivors.lean#L56-L61

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivors
open LightOriginalBucketFilter LightOriginalCollisionCleanup
attribute [local instance] Classical.propDecidable

theorem ThreeSum.LightOriginalSurvivors.sorted {keys : ℕ → ℕ} {n : ℕ} (values : ℕ → ℤ)
    (hs : ∀ i j, i < j → j < n → values i < values j) :
    ∀ i j, i < j → j < (indices keys n).length →
      values (index keys n i) < values (index keys n j) := by sorry
