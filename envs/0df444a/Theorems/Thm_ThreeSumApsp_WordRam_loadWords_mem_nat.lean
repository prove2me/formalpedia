-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_loadWords_mem_nat
-- name    : ThreeSumApsp.WordRam.loadWords_mem_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:39:44.887235+00:00
-- url     : https://prove2.me/theorems/638dbd5b-7322-411b-a723-79636cfb98f7
-- title:
--   Word Ram: load Words mem nat
-- statement:
--   The initial memory holds the input in the cells 0, 1, 2, …, followed by zeros.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L82-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L82-L84

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

theorem ThreeSumApsp.WordRam.loadWords_mem_nat (W : ℕ) (ws : List ℤ) (a : ℕ) :
    loadWords W ws (a : ℤ) = wd W (ws.getD a 0) := by sorry
