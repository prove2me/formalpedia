-- Prove2me | Theorems.Thm_ThreeSum_LightDownsetSize_program_procs
-- name    : ThreeSum.LightDownsetSize.program_procs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:37:04.905386+00:00
-- url     : https://prove2.me/theorems/5d8b7a51-cc37-447d-854c-9a06f5644f09
-- title:
--   Light Downset Size: program procs
-- statement:
--   The Light Downset Size construction uses the program procs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetSize.lean#L88-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetSize.lean#L88-L89

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_procs

set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetSize
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightDownsetSize.program_procs : LightSubsetSetup.Procs program 1 2 3 4 5 6 7 := by sorry
