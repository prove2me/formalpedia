-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_mono
-- name    : ThreeSumApsp.WordRam.AgreeOutside.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:58:17.58243+00:00
-- url     : https://prove2.me/theorems/3cb9b215-a994-4784-8d0b-d470c2a05091
-- title:
--   Agree Outside: mono
-- statement:
--   The Agree Outside construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L373-L374
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L373-L374

import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
variable {W : ℕ} {P : List Instr}
variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}

theorem ThreeSumApsp.WordRam.AgreeOutside.mono (h : AgreeOutside s m m') (hst : s ⊆ t) : AgreeOutside t m m' := by sorry
