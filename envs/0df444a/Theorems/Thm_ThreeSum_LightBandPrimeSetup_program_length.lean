-- Prove2me | Theorems.Thm_ThreeSum_LightBandPrimeSetup_program_length
-- name    : ThreeSum.LightBandPrimeSetup.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:12:54.302116+00:00
-- url     : https://prove2.me/theorems/f83b2023-41b0-4258-a5ca-e8cbea2eba3d
-- title:
--   Light Band Prime Setup: program length
-- statement:
--   The Light Band Prime Setup construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeSetup.lean#L26-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeSetup.lean#L26-L26

import Definitions.Def_Submission_ThreeSum_LightBandPrimeDepth
import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
import Theorems.Thm_ThreeSum_LightBandPrimeChain_program_length
import Theorems.Thm_ThreeSum_LightBandPrimeConstruction_program_length
import Theorems.Thm_ThreeSum_LightBandPrimeMinimum_program_length
import Theorems.Thm_ThreeSum_LightBandWeightedScoreCell_program_length
import Theorems.Thm_ThreeSum_LightBandWeightedScore_program_length

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeSetup
open Light BandCandidateRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000

theorem ThreeSum.LightBandPrimeSetup.program_length : program.length=25 := by sorry
