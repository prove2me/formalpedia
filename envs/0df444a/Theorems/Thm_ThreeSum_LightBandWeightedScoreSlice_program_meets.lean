-- Prove2me | Theorems.Thm_ThreeSum_LightBandWeightedScoreSlice_program_meets
-- name    : ThreeSum.LightBandWeightedScoreSlice.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:32:54.727077+00:00
-- url     : https://prove2.me/theorems/e9662719-b894-4eb9-bdf6-c0efc7d62acf
-- title:
--   Light Band Weighted Score Slice: program meets
-- statement:
--   The Light Band Weighted Score Slice construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandWeightedScoreSlice.lean#L45-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandWeightedScoreSlice.lean#L45-L49

import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_LightBandWeightedScoreSlice
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightPrimeChain_program_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightWeightedScore_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandWeightedScoreSlice
open Light
set_option maxHeartbeats 900000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}

theorem ThreeSum.LightBandWeightedScoreSlice.program_meets {n g i : ℕ}
    (hg : 0 < g) (hi : i*g ≤ n) (hword : ((n+g+4 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim program 0 d [n,g,i] μ time
      (fun r ν => r=(BandWeightedScore.length n g i : ℤ) ∧ ν=μ) := by sorry
