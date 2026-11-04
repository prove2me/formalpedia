-- Prove2me | Theorems.Thm_ThreeSum_LightCoverKeys_program_length
-- name    : ThreeSum.LightCoverKeys.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:10.59645+00:00
-- url     : https://prove2.me/theorems/43f7a5ab-7192-4f63-89dd-e43839b6ccd0
-- title:
--   Light Cover Keys: program length
-- statement:
--   The Light Cover Keys construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverKeys.lean#L179-L179
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverKeys.lean#L179-L179

import Definitions.Def_Submission_ThreeSum_LightLocalCoverRetention
import Definitions.Def_Submission_ThreeSum_LightGlobalKeys
import Definitions.Def_Submission_ThreeSum_LightCoverKeys
import Theorems.Thm_ThreeSum_LightGlobalKeys_program_length

set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverKeys
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightCoverKeys.program_length : program.length=68 := by sorry
