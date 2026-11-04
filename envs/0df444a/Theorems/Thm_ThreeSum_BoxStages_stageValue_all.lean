-- Prove2me | Theorems.Thm_ThreeSum_BoxStages_stageValue_all
-- name    : ThreeSum.BoxStages.stageValue_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:04:07.455286+00:00
-- url     : https://prove2.me/theorems/4c3a0a29-4ad3-4a29-a629-ab9c1c1597d6
-- title:
--   Box Stages: stage Value all
-- statement:
--   The Box Stages construction uses the stage Value all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BoxStages.lean#L55-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BoxStages.lean#L55-L59

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_Submission_ThreeSum_BoxStages
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_all
attribute [local simp] ThreeSum.SubsetStages.stageValue_all


set_option autoImplicit false
open ThreeSum ThreeSum.BoxStages
open Finset

theorem ThreeSum.BoxStages.stageValue_all {L : ℕ} (f : Finset (Fin L) → ℤ) :
    stageValue f L = Subset.zeta f := by sorry
