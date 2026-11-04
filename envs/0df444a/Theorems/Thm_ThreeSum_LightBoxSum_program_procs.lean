-- Prove2me | Theorems.Thm_ThreeSum_LightBoxSum_program_procs
-- name    : ThreeSum.LightBoxSum.program_procs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:11:03.259208+00:00
-- url     : https://prove2.me/theorems/e1095527-ed18-4385-8658-096ab249c8eb
-- title:
--   Light Box Sum: program procs
-- statement:
--   The Light Box Sum construction uses the program procs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxSum.lean#L158-L159
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxSum.lean#L158-L159

import Definitions.Def_Submission_ThreeSum_LightQueryBox
import Definitions.Def_Submission_ThreeSum_BoxBounds
import Definitions.Def_Submission_ThreeSum_LightBoxSum
import Theorems.Thm_ThreeSum_LightBoxStages_program_procs
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_procs
import Theorems.Thm_ThreeSum_LightDownsetSize_program_procs
import Theorems.Thm_ThreeSum_LightQueryBox_program_procs
import Theorems.Thm_ThreeSum_LightStageLookup_program_procs
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_procs
import Theorems.Thm_ThreeSum_LightZetaCell_program_procs
import Theorems.Thm_ThreeSum_LightZetaPass_program_procs
import Theorems.Thm_ThreeSum_LightZetaStages_program_procs

set_option autoImplicit false
open ThreeSum ThreeSum.LightBoxSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBoxSum.program_procs : LightSubsetSetup.Procs program 6 7 8 13 14 9 10 := by sorry
