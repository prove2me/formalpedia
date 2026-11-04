-- Prove2me | Theorems.Thm_ThreeSum_LightZetaPass_program_procs
-- name    : ThreeSum.LightZetaPass.program_procs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:43:16.657565+00:00
-- url     : https://prove2.me/theorems/2073a5e8-b6b2-498b-abfc-28aaebc38f72
-- title:
--   Light Zeta Pass: program procs
-- statement:
--   The Light Zeta Pass construction uses the program procs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaPass.lean#L160-L161
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaPass.lean#L160-L161

import Definitions.Def_Submission_ThreeSum_LightZetaBatch
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_procs
import Theorems.Thm_ThreeSum_LightZetaCell_program_procs

set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaPass
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightZetaPass.program_procs : LightSubsetSetup.Procs program 4 5 6 7 8 9 10 := by sorry
