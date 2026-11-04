-- Prove2me | Theorems.Thm_ThreeSum_LightBandPrimeMinimum_program_length
-- name    : ThreeSum.LightBandPrimeMinimum.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:44:28.209423+00:00
-- url     : https://prove2.me/theorems/3dd986eb-dd04-49e7-9183-4fb0bf61b1f4
-- title:
--   Light Band Prime Minimum: program length
-- statement:
--   The Light Band Prime Minimum construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeMinimum.lean#L29-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeMinimum.lean#L29-L29

import Definitions.Def_Submission_ThreeSum_LightBandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandPrimeChoice
import Definitions.Def_Submission_ThreeSum_LightBandPrimeMinimum
import Theorems.Thm_ThreeSum_LightBandWeightedScoreCell_program_length
import Theorems.Thm_ThreeSum_LightBandWeightedScore_program_length

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeMinimum
open Light BandCandidateRows BandWeightedScore BandPrimeChoice
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

theorem ThreeSum.LightBandPrimeMinimum.program_length : program.length=18 := by sorry
