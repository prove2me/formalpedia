-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_codeAt_self
-- name    : ThreeSumApsp.WordRam.codeAt_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:01:40.582161+00:00
-- url     : https://prove2.me/theorems/8637df29-684c-4c13-b4c8-2a292effade5
-- title:
--   Word Ram: code At self
-- statement:
--   The whole program, from position 0 on.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L192-L192
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L192-L192

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

theorem ThreeSumApsp.WordRam.codeAt_self (l : List Instr) : CodeAt l 0 l := by sorry
