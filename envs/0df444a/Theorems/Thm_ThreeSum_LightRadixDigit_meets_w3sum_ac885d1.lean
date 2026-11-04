-- Prove2me | Theorems.Thm_ThreeSum_LightRadixDigit_meets_w3sum_ac885d1
-- name    : ThreeSum.LightRadixDigit.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:10.452204+00:00
-- url     : https://prove2.me/theorems/39515a38-2c83-47db-b1a0-98a13e1a34b4
-- title:
--   Light Radix Digit: meets
-- statement:
--   The Light Radix Digit construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixDigit.lean#L19-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixDigit.lean#L19-L82

import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixDigit
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightRadixDigit.meets_w3sum_ac885d1 {pMain pDivide k b p : ℕ}
    (hmain : P[pMain]? = some (body pDivide))
    (hdivide : P[pDivide]? = some LightSmallDivide.body) (μ : ℕ → ℤ)
    (hd : d < lim.depth) (hword : (word k b p : ℤ) ≤ lim.word) :
    Meets lim P pMain d [k,b,p] μ (time k)
      (fun r μ' => r = (((k/b)%p : ℕ) : ℤ) ∧ μ'=μ) := by sorry
