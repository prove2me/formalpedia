-- Prove2me | Theorems.Thm_ThreeSum_LightBandWeightedScoreSlice_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBandWeightedScoreSlice.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:29:50.957366+00:00
-- url     : https://prove2.me/theorems/badfb9db-9d49-48c6-ad11-01bd844492ed
-- title:
--   Light Band Weighted Score Slice: meets
-- statement:
--   The Light Band Weighted Score Slice construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandWeightedScoreSlice.lean#L21-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandWeightedScoreSlice.lean#L21-L41

import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_LightBandWeightedScoreSlice
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Theorems.Thm_ThreeSum_LightPrimeChain_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Definitions.Def_WeightedCache3SUM_Alias_280261ae8ac7fab5

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandWeightedScoreSlice
open Light
set_option maxHeartbeats 900000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}

theorem ThreeSum.LightBandWeightedScoreSlice.meets_w3sum_ac885d1 {pMain n g i : ℕ} (hmain : P[pMain]?=some body)
    (hg : 0 < g) (hi : i*g ≤ n) (hword : ((n+g+4 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pMain d [n,g,i] μ time
      (fun r ν => r=(BandWeightedScore.length n g i : ℤ) ∧ ν=μ) := by sorry
