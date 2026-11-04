-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_loadWords_mem_neg
-- name    : ThreeSumApsp.WordRam.loadWords_mem_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:39:50.247364+00:00
-- url     : https://prove2.me/theorems/71c0822f-4093-442b-b2a3-47cd943b5317
-- title:
--   Word Ram: load Words mem neg
-- statement:
--   The negative cells of the initial memory hold zeros.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L87-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L87-L89

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

theorem ThreeSumApsp.WordRam.loadWords_mem_neg (W : ℕ) (ws : List ℤ) {a : ℤ} (ha : a < 0) :
    loadWords W ws a = wd W 0 := by sorry
