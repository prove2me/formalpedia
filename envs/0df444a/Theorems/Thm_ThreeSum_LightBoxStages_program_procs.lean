-- Prove2me | Theorems.Thm_ThreeSum_LightBoxStages_program_procs
-- name    : ThreeSum.LightBoxStages.program_procs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:49:09.029571+00:00
-- url     : https://prove2.me/theorems/ae76b987-8df6-42b5-8192-0b1678bf7e38
-- title:
--   Light Box Stages: program procs
-- statement:
--   The Light Box Stages construction uses the program procs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxStages.lean#L175-L176
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxStages.lean#L175-L176

import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_Submission_ThreeSum_LightBoxStages
import Theorems.Thm_ThreeSum_LightDownsetSize_program_procs
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_procs
import Theorems.Thm_ThreeSum_LightZetaCell_program_procs
import Theorems.Thm_ThreeSum_LightZetaPass_program_procs

set_option autoImplicit false
open ThreeSum ThreeSum.LightBoxStages
open Light ThreeSum.SubsetAddress ThreeSum.BoxStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBoxStages.program_procs : LightSubsetSetup.Procs program 6 7 8 9 10 11 12 := by sorry
