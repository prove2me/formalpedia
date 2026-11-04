-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_exec_zero
-- name    : ThreeSumApsp.WordRam.exec_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:39:53.212975+00:00
-- url     : https://prove2.me/theorems/078041db-9539-41c0-b2dc-d8cd4862a519
-- title:
--   Word Ram: exec zero
-- statement:
--   Within no steps there is no verdict.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L144-L144
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L144-L144

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

theorem ThreeSumApsp.WordRam.exec_zero (c : Cfg W) : exec P 0 c.pc c.mem = none := by sorry
