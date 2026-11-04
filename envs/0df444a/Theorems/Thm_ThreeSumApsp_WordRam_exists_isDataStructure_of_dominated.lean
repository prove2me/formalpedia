-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_exists_isDataStructure_of_dominated
-- name    : ThreeSumApsp.WordRam.exists_isDataStructure_of_dominated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:34.742816+00:00
-- url     : https://prove2.me/theorems/34bca118-7d90-435c-a51c-4cf29d899612
-- title:
--   Word Ram: exists is Data Structure of dominated
-- statement:
--   A data structure with the bounds `O(f)`, `O(f)`, `O(g)` is one with the bounds `O(f')`, `O(f')`,
--   `O(g')` if `f = O(f')` and `g = O(g')`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L139-L156
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L139-L156

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

theorem ThreeSumApsp.WordRam.exists_isDataStructure_of_dominated {dom dom' : ThinPair → Prop}
    {f f' g g' : ThinPair → ℝ}
    (h : ∃ (P Q : List Instr) (qI qJ qOut : ℤ) (b : ℕ) (C : ℝ), IsDataStructure P Q qI qJ qOut b []
      dom (fun x => C * f x) (fun x => C * f x) (fun x => C * g x))
    (hdom : ∀ x, dom' x → dom x) (hf : Dominated dom' f f') (hg : Dominated dom' g g')
    (hf0 : ∀ x, dom' x → 0 ≤ f x := by intro _ _; positivity)
    (hg0 : ∀ x, dom' x → 0 ≤ g x := by intro _ _; positivity)
    (hf'0 : ∀ x, dom' x → 0 ≤ f' x := by intro _ _; positivity)
    (hg'0 : ∀ x, dom' x → 0 ≤ g' x := by intro _ _; positivity) :
    ∃ (P Q : List Instr) (qI qJ qOut : ℤ) (b : ℕ) (C : ℝ), IsDataStructure P Q qI qJ qOut b []
      dom' (fun x => C * f' x) (fun x => C * f' x) (fun x => C * g' x) := by sorry
