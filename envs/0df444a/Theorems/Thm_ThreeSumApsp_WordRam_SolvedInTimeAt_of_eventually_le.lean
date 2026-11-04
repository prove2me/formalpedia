-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_SolvedInTimeAt_of_eventually_le
-- name    : ThreeSumApsp.WordRam.SolvedInTimeAt.of_eventually_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:07:39.298869+00:00
-- url     : https://prove2.me/theorems/7d8b2390-51bb-4f8f-919f-2915f8f2ea9b
-- title:
--   Solved In Time At: of eventually le
-- statement:
--   The bound `O(n^a (log n)^e)` may be replaced by a bound `O(n^a' (log n)^e')` that is at least as
--   large, up to a constant, for all large `n`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L162-L172
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L162-L172

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

theorem ThreeSumApsp.WordRam.SolvedInTimeAt.of_eventually_le {Q : EndStatement.Problem} {κ : ℕ} {a a' C : ℝ} {e e' : ℕ}
    (h : SolvedInTimeAt Q κ a e)
    (hle : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ a * Real.log n ^ e ≤ C * ((n : ℝ) ^ a' * Real.log n ^ e')) :
    SolvedInTimeAt Q κ a' e' := by sorry
