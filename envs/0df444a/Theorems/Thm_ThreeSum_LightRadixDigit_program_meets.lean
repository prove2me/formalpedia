-- Prove2me | Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
-- name    : ThreeSum.LightRadixDigit.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:19:10.668183+00:00
-- url     : https://prove2.me/theorems/efdaeea0-39fc-4ec5-8651-3743622da127
-- title:
--   Light Radix Digit: program meets
-- statement:
--   The Light Radix Digit construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixDigit.lean#L86-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixDigit.lean#L86-L90

import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixDigit
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightRadixDigit.program_meets {k b p : ℕ} (μ : ℕ → ℤ)
    (hd : d < lim.depth) (hword : (word k b p : ℤ) ≤ lim.word) :
    Meets lim program 0 d [k,b,p] μ (time k)
      (fun r μ' => r = (((k/b)%p : ℕ) : ℤ) ∧ μ'=μ) := by sorry
