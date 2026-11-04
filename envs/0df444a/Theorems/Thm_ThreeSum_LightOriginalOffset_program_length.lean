-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalOffset_program_length
-- name    : ThreeSum.LightOriginalOffset.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:44:34.700196+00:00
-- url     : https://prove2.me/theorems/aa3157ed-050a-4bc3-8fcc-b5ba7618b508
-- title:
--   Light Original Offset: program length
-- statement:
--   The Light Original Offset construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalOffset.lean#L194-L194
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalOffset.lean#L194-L194

import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset
set_option autoImplicit false
open ThreeSum ThreeSum.LightOriginalOffset
open Light LightResidues LightResidueHistogram
open KaratsubaInterface CyclicFold
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightOriginalOffset.program_length : program.length = 13 := by sorry
