-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_Bounded_abs_le
-- name    : ThreeSumApsp.WordRam.Bounded.abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:25.79498+00:00
-- url     : https://prove2.me/theorems/d9ff3e65-d019-48c3-a7ec-068f920c5886
-- title:
--   Bounded: abs le
-- statement:
--   The numbers of the input of a bounded instance are within the bound.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L53-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L53-L56

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr)
open Filter

theorem ThreeSumApsp.WordRam.Bounded.abs_le {Q : EndStatement.Problem} {x : Bounded Q} {a : ℤ} (ha : a ∈ Q.input x.x) :
    |a| ≤ (x.U : ℤ) := by sorry
