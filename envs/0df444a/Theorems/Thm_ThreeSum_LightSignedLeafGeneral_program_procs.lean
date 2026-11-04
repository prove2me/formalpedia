-- Prove2me | Theorems.Thm_ThreeSum_LightSignedLeafGeneral_program_procs
-- name    : ThreeSum.LightSignedLeafGeneral.program_procs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:33.917803+00:00
-- url     : https://prove2.me/theorems/6f8ddd19-8f3e-4ea6-83ca-6e6bcb54e38a
-- title:
--   Light Signed Leaf General: program procs
-- statement:
--   The Light Signed Leaf General construction uses the program procs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafGeneral.lean#L144-L145
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafGeneral.lean#L144-L145

import Definitions.Def_Submission_ThreeSum_LightSignedLeaf
import Definitions.Def_Submission_ThreeSum_LightMaskUnion
import Definitions.Def_Submission_ThreeSum_LightSignedLeafGeneral
import Theorems.Thm_ThreeSum_LightBoxStages_program_procs
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_procs
import Theorems.Thm_ThreeSum_LightDownsetSize_program_procs
import Theorems.Thm_ThreeSum_LightSignedLeaf_program_procs
import Theorems.Thm_ThreeSum_LightStageLookup_program_procs
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_procs
import Theorems.Thm_ThreeSum_LightZetaCell_program_procs
import Theorems.Thm_ThreeSum_LightZetaPass_program_procs
import Theorems.Thm_ThreeSum_LightZetaStages_program_procs

set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedLeafGeneral
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSignedLeafGeneral.program_procs : LightSubsetSetup.Procs program 5 6 7 8 9 10 11 := by sorry
