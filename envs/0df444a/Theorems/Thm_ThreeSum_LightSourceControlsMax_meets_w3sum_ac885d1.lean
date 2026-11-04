-- Prove2me | Theorems.Thm_ThreeSum_LightSourceControlsMax_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSourceControlsMax.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:33:25.436073+00:00
-- url     : https://prove2.me/theorems/39f9c739-0b6b-4a58-b51a-b4b1227d6bd9
-- title:
--   Light Source Controls Max: meets
-- statement:
--   The Light Source Controls Max construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceControlsMax.lean#L13-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceControlsMax.lean#L13-L26

import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightSourceControlsMax
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceControlsMax
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceControlsMax.meets_w3sum_ac885d1 {p a b : ℕ} (hp : P[p]?=some body) (μ : ℕ → ℤ)
    (hword : ((max a b : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [a,b] μ 40 (fun r ν => r=((max a b : ℕ) : ℤ) ∧ ν=μ) := by sorry
