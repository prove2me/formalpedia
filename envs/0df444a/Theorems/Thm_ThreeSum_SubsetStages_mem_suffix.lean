-- Prove2me | Theorems.Thm_ThreeSum_SubsetStages_mem_suffix
-- name    : ThreeSum.SubsetStages.mem_suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:51:24.777545+00:00
-- url     : https://prove2.me/theorems/b1fb4d90-aeb6-4461-8856-a92665f54f52
-- title:
--   Subset Stages: mem suffix
-- statement:
--   The Subset Stages construction uses the mem suffix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetStages.lean#L19-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetStages.lean#L19-L20

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_SubsetStages
set_option autoImplicit false
open ThreeSum ThreeSum.SubsetStages
open Finset

theorem ThreeSum.SubsetStages.mem_suffix {L j : ℕ} (a : Fin L) : a ∈ suffix L j ↔ L-j ≤ a.val := by sorry
