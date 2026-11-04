-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryNearPair_program_length
-- name    : ThreeSum.LightTernaryNearPair.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:09:21.947288+00:00
-- url     : https://prove2.me/theorems/0e005c53-29a1-469c-a9c9-65f66a018849
-- title:
--   Light Ternary Near Pair: program length
-- statement:
--   The Light Ternary Near Pair construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearPair.lean#L236-L236
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearPair.lean#L236-L236

import Definitions.Def_Submission_ThreeSum_LightTernaryNearSourceWords
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryNearPair
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000

theorem ThreeSum.LightTernaryNearPair.program_length : program.length=19 := by sorry

attribute [defeq] ThreeSum.LightTernaryNearPair.program_length
