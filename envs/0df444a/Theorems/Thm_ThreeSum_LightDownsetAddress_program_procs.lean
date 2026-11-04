-- Prove2me | Theorems.Thm_ThreeSum_LightDownsetAddress_program_procs
-- name    : ThreeSum.LightDownsetAddress.program_procs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:37:11.529993+00:00
-- url     : https://prove2.me/theorems/bb9f5624-f0e7-4477-84cb-7cc30dfdc823
-- title:
--   Light Downset Address: program procs
-- statement:
--   The Light Downset Address construction uses the program procs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetAddress.lean#L77-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetAddress.lean#L77-L78

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_LightDownsetAddress
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_procs

set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetAddress
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightDownsetAddress.program_procs : LightSubsetSetup.Procs program 1 2 3 4 5 6 7 := by sorry
