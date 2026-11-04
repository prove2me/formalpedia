-- Prove2me | Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
-- name    : ThreeSum.LightSmallDivide.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:39:06.183416+00:00
-- url     : https://prove2.me/theorems/7fc016ff-14e7-464f-ae05-b6127c0730ab
-- title:
--   Light Small Divide: program meets
-- statement:
--   The Light Small Divide construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSmallDivide.lean#L80-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSmallDivide.lean#L80-L84

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
set_option autoImplicit false
open ThreeSum ThreeSum.LightSmallDivide
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSmallDivide.program_meets {a b : ℕ} (μ : ℕ → ℤ)
    (hword : ((a+b+2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim program 0 d [a,b] μ (time a b)
      (fun r μ' => r = ((a/b : ℕ) : ℤ) ∧ μ' = μ) := by sorry
