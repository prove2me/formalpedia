-- Prove2me | Theorems.Thm_ThreeSum_LightSignedLeaf_program_procs
-- name    : ThreeSum.LightSignedLeaf.program_procs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:45.683442+00:00
-- url     : https://prove2.me/theorems/59d3f4ba-4725-48c7-b434-a46e144851ee
-- title:
--   Light Signed Leaf: program procs
-- statement:
--   The Light Signed Leaf construction uses the program procs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeaf.lean#L117-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeaf.lean#L117-L118

import Definitions.Def_Submission_ThreeSum_SignedLeaf
import Definitions.Def_Submission_ThreeSum_LightStageLookup
import Definitions.Def_Submission_ThreeSum_LightSign
import Definitions.Def_Submission_ThreeSum_LightSignedLeaf
import Theorems.Thm_ThreeSum_LightBoxStages_program_procs
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_procs
import Theorems.Thm_ThreeSum_LightDownsetSize_program_procs
import Theorems.Thm_ThreeSum_LightStageLookup_program_procs
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_procs
import Theorems.Thm_ThreeSum_LightZetaCell_program_procs
import Theorems.Thm_ThreeSum_LightZetaPass_program_procs
import Theorems.Thm_ThreeSum_LightZetaStages_program_procs

set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedLeaf
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSignedLeaf.program_procs : LightSubsetSetup.Procs program 4 5 6 7 8 9 10 := by sorry
