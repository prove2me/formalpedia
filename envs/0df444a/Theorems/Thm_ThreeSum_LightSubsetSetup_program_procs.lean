-- Prove2me | Theorems.Thm_ThreeSum_LightSubsetSetup_program_procs
-- name    : ThreeSum.LightSubsetSetup.program_procs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:30:33.401328+00:00
-- url     : https://prove2.me/theorems/ce6cb72b-1f19-4789-9120-2a68ab1d20cc
-- title:
--   Light Subset Setup: program procs
-- statement:
--   The Light Subset Setup construction uses the program procs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetSetup.lean#L84-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetSetup.lean#L84-L85

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSubsetSetup.program_procs : Procs program 0 1 2 3 4 5 6 := by sorry
