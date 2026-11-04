-- Prove2me | Theorems.Thm_ThreeSum_LightBandPrimeDepth_program_meets
-- name    : ThreeSum.LightBandPrimeDepth.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:58:26.991122+00:00
-- url     : https://prove2.me/theorems/93516714-fb40-48e5-b824-8e8cfa1bff6c
-- title:
--   Light Band Prime Depth: program meets
-- statement:
--   The Light Band Prime Depth construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeDepth.lean#L109-L111
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeDepth.lean#L109-L111

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightBandPrimeDepth
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeDepth
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {R y : ℕ}

theorem ThreeSum.LightBandPrimeDepth.program_meets (hy : 0 < y) (hword : (word R y : ℤ) ≤ lim.word) :
    Meets lim program 0 d [R,y] μ (time R y)
      (fun result ν => result=(depth R y : ℤ) ∧ ν=μ) := by sorry
