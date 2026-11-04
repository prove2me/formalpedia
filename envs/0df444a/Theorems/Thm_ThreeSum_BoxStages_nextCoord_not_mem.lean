-- Prove2me | Theorems.Thm_ThreeSum_BoxStages_nextCoord_not_mem
-- name    : ThreeSum.BoxStages.nextCoord_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:16:43.271041+00:00
-- url     : https://prove2.me/theorems/1864cbbf-abd6-4590-b2dc-8e3c8ffe68c9
-- title:
--   Box Stages: next Coord not mem
-- statement:
--   The Box Stages construction uses the next Coord not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BoxStages.lean#L33-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BoxStages.lean#L33-L34

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_Submission_ThreeSum_BoxStages
import Theorems.Thm_ThreeSum_SubsetStages_nextCoord_not_mem

set_option autoImplicit false
open ThreeSum ThreeSum.BoxStages
open Finset

theorem ThreeSum.BoxStages.nextCoord_not_mem {L j : ℕ} (hj : j < L) : nextCoord j hj ∉ initialCoords L j := by sorry
