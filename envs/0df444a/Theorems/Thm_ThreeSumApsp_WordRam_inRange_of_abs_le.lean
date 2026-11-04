-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_inRange_of_abs_le
-- name    : ThreeSumApsp.WordRam.inRange_of_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:39:38.735634+00:00
-- url     : https://prove2.me/theorems/b53b4e69-d929-4fb7-b749-7000f4dc896d
-- title:
--   Word Ram: in Range of abs le
-- statement:
--   Numbers of absolute value at most B are in the range of words if 2 B < 2^W.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L77-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L77-L79

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

theorem ThreeSumApsp.WordRam.inRange_of_abs_le {v B : ℤ} (hB : 2 * B < (2 : ℤ) ^ W) (h : |v| ≤ B) : InRange W v := by sorry
