-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalDigitLength_clog_meets
-- name    : ThreeSum.LightWeightedGlobalDigitLength.clog_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:27:11.963136+00:00
-- url     : https://prove2.me/theorems/85e9f5bd-9a50-475a-91ec-dc8219ecc8d6
-- title:
--   Light Weighted Global Digit Length: clog meets
-- statement:
--   The Light Weighted Global Digit Length construction uses the clog meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDigitLength.lean#L28-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDigitLength.lean#L28-L68

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_Weighted_Global_LightTernaryDigitLength
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalDigitLength
open Light WeightedGlobalSignedPadding
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightWeightedGlobalDigitLength.clog_meets {p b x : ℕ} (hp : P[p]?=some clogBody) (μ : ℕ→ℤ)
    (hb : 1<b) (hx : 0<x) (hword : (word b x : ℤ)≤lim.word) :
    Meets lim P p d [x,b] μ (clogTime b x)
      (fun r ν => r=(Nat.clog b x : ℤ) ∧ ν=μ) := by sorry
