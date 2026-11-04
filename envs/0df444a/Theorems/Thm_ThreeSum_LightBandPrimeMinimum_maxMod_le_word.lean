-- Prove2me | Theorems.Thm_ThreeSum_LightBandPrimeMinimum_maxMod_le_word
-- name    : ThreeSum.LightBandPrimeMinimum.maxMod_le_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:34:25.094328+00:00
-- url     : https://prove2.me/theorems/7c2a1049-e3fa-4e52-9d49-6ef9bfbdd13c
-- title:
--   Light Band Prime Minimum: max Mod le word
-- statement:
--   The Light Band Prime Minimum construction uses the max Mod le word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeMinimum.lean#L41-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeMinimum.lean#L41-L44

import Definitions.Def_Submission_ThreeSum_LightBandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandPrimeChoice
import Definitions.Def_Submission_ThreeSum_LightBandPrimeMinimum
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeMinimum
open Light BandCandidateRows BandWeightedScore BandPrimeChoice
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

theorem ThreeSum.LightBandPrimeMinimum.maxMod_le_word (maxMod nA nB nC g R s U : ℕ) :
    maxMod ≤ LightBandWeightedScore.word maxMod nA nB nC g R s U := by sorry
