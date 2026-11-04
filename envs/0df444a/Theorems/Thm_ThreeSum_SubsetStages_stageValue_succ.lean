-- Prove2me | Theorems.Thm_ThreeSum_SubsetStages_stageValue_succ
-- name    : ThreeSum.SubsetStages.stageValue_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:02:53.537246+00:00
-- url     : https://prove2.me/theorems/7450903d-0f2f-4a08-a4d1-efec3aecfdb6
-- title:
--   Subset Stages: stage Value succ
-- statement:
--   The Subset Stages construction uses the stage Value succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetStages.lean#L50-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetStages.lean#L50-L54

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_SubsetStages
set_option autoImplicit false
open ThreeSum ThreeSum.SubsetStages
open Finset

theorem ThreeSum.SubsetStages.stageValue_succ {L j : ℕ} (f : Finset (Fin L) → ℤ) (hj : j < L) :
    stageValue f (j+1) = Subset.zetaStep (nextCoord j hj) (stageValue f j) := by sorry
