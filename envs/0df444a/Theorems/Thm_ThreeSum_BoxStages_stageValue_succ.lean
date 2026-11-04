-- Prove2me | Theorems.Thm_ThreeSum_BoxStages_stageValue_succ
-- name    : ThreeSum.BoxStages.stageValue_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:41:08.944096+00:00
-- url     : https://prove2.me/theorems/657aec85-c94f-49ae-a9ce-c1e917c7b50d
-- title:
--   Box Stages: stage Value succ
-- statement:
--   The Box Stages construction uses the stage Value succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BoxStages.lean#L49-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BoxStages.lean#L49-L53

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_Submission_ThreeSum_BoxStages
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_succ

set_option autoImplicit false
open ThreeSum ThreeSum.BoxStages
open Finset

theorem ThreeSum.BoxStages.stageValue_succ {L j : ℕ} (f : Finset (Fin L) → ℤ) (hj : j < L) :
    stageValue f (j+1) = Subset.zetaStep (nextCoord j hj) (stageValue f j) := by sorry
