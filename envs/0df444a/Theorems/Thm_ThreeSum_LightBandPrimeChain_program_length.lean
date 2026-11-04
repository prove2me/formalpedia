-- Prove2me | Theorems.Thm_ThreeSum_LightBandPrimeChain_program_length
-- name    : ThreeSum.LightBandPrimeChain.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:54:27.61319+00:00
-- url     : https://prove2.me/theorems/c8cff9f4-b7db-4bcb-97f8-54bef82c576e
-- title:
--   Light Band Prime Chain: program length
-- statement:
--   The Light Band Prime Chain construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeChain.lean#L33-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeChain.lean#L33-L33

import Definitions.Def_Submission_ThreeSum_LightBandPrimeMinimum
import Definitions.Def_Submission_ThreeSum_LightBandPrimeChain
import Theorems.Thm_ThreeSum_LightBandPrimeMinimum_program_length
import Theorems.Thm_ThreeSum_LightBandWeightedScoreCell_program_length
import Theorems.Thm_ThreeSum_LightBandWeightedScore_program_length

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeChain
open Light BandCandidateRows BandPrimeChoice
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

theorem ThreeSum.LightBandPrimeChain.program_length : program.length=19 := by sorry
