-- Prove2me | Theorems.Thm_ThreeSum_BoxStages_stageValue_eq_boxSum
-- name    : ThreeSum.BoxStages.stageValue_eq_boxSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:22:46.033674+00:00
-- url     : https://prove2.me/theorems/699c083e-bc34-4d6f-babb-a3ac5c629e4f
-- title:
--   Box Stages: stage Value eq box Sum
-- statement:
--   The Box Stages construction uses the stage Value eq box Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BoxStages.lean#L135-L138
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BoxStages.lean#L135-L138

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_Submission_ThreeSum_BoxStages
set_option autoImplicit false
open ThreeSum ThreeSum.BoxStages
open Finset

theorem ThreeSum.BoxStages.stageValue_eq_boxSum {L : ℕ} (weight : Finset (Fin L) → ℤ)
    (j : ℕ) (flags : Finset (Fin L)) :
    stageValue weight j flags = SparseBoxes.boxSum flags (flags ∩ initialCoords L j) weight := by sorry
