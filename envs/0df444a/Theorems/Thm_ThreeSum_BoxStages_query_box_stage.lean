-- Prove2me | Theorems.Thm_ThreeSum_BoxStages_query_box_stage
-- name    : ThreeSum.BoxStages.query_box_stage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:16:42.874611+00:00
-- url     : https://prove2.me/theorems/bb72ae6c-eff7-4532-8d3c-38b4727ec470
-- title:
--   Box Stages: query box stage
-- statement:
--   The Box Stages construction uses the query box stage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BoxStages.lean#L147-L151
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BoxStages.lean#L147-L151

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_Submission_ThreeSum_BoxStages
set_option autoImplicit false
open ThreeSum ThreeSum.BoxStages
open Finset

theorem ThreeSum.BoxStages.query_box_stage {L : ℕ} (weight : Finset (Fin L) → ℤ)
    (q u : Finset (Fin L)) (hu : u.Nonempty) :
    SparseBoxes.boxSum (q \ u) (SparseBoxes.queryFree q u) weight =
      stageValue weight (u.min' hu).val (q \ u) := by sorry
