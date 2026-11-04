-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_toInt_wd
-- name    : ThreeSumApsp.WordRam.toInt_wd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:08.898194+00:00
-- url     : https://prove2.me/theorems/cece10fa-9470-4271-9104-37dd18eec37f
-- title:
--   Word Ram: to Int wd
-- statement:
--   The word of a number in the range of words, read as a signed number, is that number.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L59-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L59-L62

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

theorem ThreeSumApsp.WordRam.toInt_wd {v : ℤ} (h : InRange W v) : (wd W v).toInt = v := by sorry
