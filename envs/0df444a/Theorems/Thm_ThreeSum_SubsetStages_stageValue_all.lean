-- Prove2me | Theorems.Thm_ThreeSum_SubsetStages_stageValue_all
-- name    : ThreeSum.SubsetStages.stageValue_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:51:29.334318+00:00
-- url     : https://prove2.me/theorems/48d04f28-0c08-4962-b840-f96b5b76b7cb
-- title:
--   Subset Stages: stage Value all
-- statement:
--   The Subset Stages construction uses the stage Value all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetStages.lean#L56-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetStages.lean#L56-L62

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_SubsetStages
set_option autoImplicit false
open ThreeSum ThreeSum.SubsetStages
open Finset

theorem ThreeSum.SubsetStages.stageValue_all {L : ℕ} (f : Finset (Fin L) → ℤ) :
    stageValue f L = Subset.zeta f := by sorry
