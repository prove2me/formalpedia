-- Prove2me | Theorems.Thm_ThreeSum_SubsetStages_nextCoord_not_mem
-- name    : ThreeSum.SubsetStages.nextCoord_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:31.700325+00:00
-- url     : https://prove2.me/theorems/1f0bee67-b21f-4967-8f6c-3e1f250a2168
-- title:
--   Subset Stages: next Coord not mem
-- statement:
--   The Subset Stages construction uses the next Coord not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetStages.lean#L33-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetStages.lean#L33-L35

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_SubsetStages
set_option autoImplicit false
open ThreeSum ThreeSum.SubsetStages
open Finset

theorem ThreeSum.SubsetStages.nextCoord_not_mem {L j : ℕ} (hj : j < L) : nextCoord j hj ∉ suffix L j := by sorry
