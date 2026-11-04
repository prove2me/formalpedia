-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_wd_toInt
-- name    : ThreeSumApsp.WordRam.wd_toInt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:39:38.628284+00:00
-- url     : https://prove2.me/theorems/eb3e3680-1762-4b7f-a60b-5a4273317546
-- title:
--   Word Ram: wd to Int
-- statement:
--   Every word is the word of its signed value.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L65-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L65-L65

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

theorem ThreeSumApsp.WordRam.wd_toInt (w : BitVec W) : wd W w.toInt = w := by sorry
