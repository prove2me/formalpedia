-- Prove2me | Theorems.Thm_ThreeSum_LightNatPower_meets_w3sum_ac885d1
-- name    : ThreeSum.LightNatPower.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:11.562242+00:00
-- url     : https://prove2.me/theorems/3cc3a70b-d218-47a4-a1c4-1cacbb5efcbe
-- title:
--   Light Nat Power: meets
-- statement:
--   The Light Nat Power construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNatPower.lean#L24-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNatPower.lean#L24-L56

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightNatPower
set_option autoImplicit false
open ThreeSum ThreeSum.LightNatPower
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightNatPower.meets_w3sum_ac885d1 {p b e : ℕ} (hp : P[p]? = some body) (μ : ℕ → ℤ)
    (he : (e : ℤ) ≤ lim.word)
    (hpow : ∀ i ≤ e, ((b^i : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [b,e] μ (time e)
      (fun r μ' => r = ((b^e : ℕ) : ℤ) ∧ μ' = μ) := by sorry
