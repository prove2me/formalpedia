-- Prove2me | Theorems.Thm_ThreeSum_LightPrimeCoefficient_mulAdd_meets
-- name    : ThreeSum.LightPrimeCoefficient.mulAdd_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:39:47.182588+00:00
-- url     : https://prove2.me/theorems/ed30361f-18b3-4ae8-8f31-0f28bb7facf3
-- title:
--   Light Prime Coefficient: mul Add meets
-- statement:
--   The Light Prime Coefficient construction uses the mul Add meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeCoefficient.lean#L21-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeCoefficient.lean#L21-L64

import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightPrimeCoefficient
set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimeCoefficient
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightPrimeCoefficient.mulAdd_meets {pMain pDivide acc x y p : ℕ}
    (hmain : P[pMain]?=some (mulAddBody pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body) (μ : ℕ → ℤ)
    (hd : d<lim.depth) (hp : 0<p) (ha : acc<p) (hx : x<p) (hy : y<p)
    (hword : (word p : ℤ)≤lim.word) :
    Meets lim P pMain d [acc,x,y,p] μ (mulAddTime p)
      (fun r ν => r=(((acc+x*y)%p : ℕ) : ℤ) ∧ ν=μ) := by sorry
