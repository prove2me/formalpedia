-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryNearSetup_program_length
-- name    : ThreeSum.LightTernaryNearSetup.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:21:19.912965+00:00
-- url     : https://prove2.me/theorems/f163a87d-bef4-41ee-89d0-04f6b1708392
-- title:
--   Light Ternary Near Setup: program length
-- statement:
--   The Light Ternary Near Setup construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearSetup.lean#L108-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearSetup.lean#L108-L108

import Definitions.Def_Submission_ThreeSum_LightTernaryNearDigits
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumerationMain
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
import Definitions.Def_Submission_ThreeSum_LightTernaryNearSetup
import Theorems.Thm_ThreeSum_LightTernaryNearPair_program_length
attribute [local simp] ThreeSum.LightTernaryNearPair.program_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearSetup
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBankEnumeration ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryNearSetup.program_length : program.length=7 := by sorry

attribute [defeq] ThreeSum.LightTernaryNearSetup.program_length
