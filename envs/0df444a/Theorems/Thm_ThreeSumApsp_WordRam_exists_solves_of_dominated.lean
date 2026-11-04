-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_exists_solves_of_dominated
-- name    : ThreeSumApsp.WordRam.exists_solves_of_dominated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:45:56.718253+00:00
-- url     : https://prove2.me/theorems/c486f2cb-5f4b-48eb-bf5e-8e39e0fa54e9
-- title:
--   Word Ram: exists solves of dominated
-- statement:
--   A program that solves a problem in time `O(f)` solves it in time `O(f')` if `f = O(f')`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L127-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L127-L135

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

theorem ThreeSumApsp.WordRam.exists_solves_of_dominated {prob : Problem} {dom dom' : prob.Inst → Prop}
    {f f' : prob.Inst → ℝ}
    (h : ∃ (P : List Instr) (b : ℕ) (C : ℝ), Solves prob P b dom fun x => C * f x)
    (hdom : ∀ x, dom' x → dom x) (hf : Dominated dom' f f')
    (hf0 : ∀ x, dom' x → 0 ≤ f x := by intro _ _; positivity) :
    ∃ (P : List Instr) (b : ℕ) (C : ℝ), Solves prob P b dom' fun x => C * f' x := by sorry
