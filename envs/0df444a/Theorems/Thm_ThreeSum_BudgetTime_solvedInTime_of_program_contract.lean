-- Prove2me | Theorems.Thm_ThreeSum_BudgetTime_solvedInTime_of_program_contract
-- name    : ThreeSum.BudgetTime.solvedInTime_of_program_contract
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:54:48.662003+00:00
-- url     : https://prove2.me/theorems/f519ce2e-647d-4e5a-a106-f3f824c00320
-- title:
--   Budget Time: solved In Time of program contract
-- statement:
--   An interface for the remaining program proof.  The hypothesis contains
--   actual machine execution and correctness at every input size and admissible
--   word width; only its cost comparison may be eventual.  No instance of this
--   hypothesis is constructed here.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BudgetTime.lean#L106-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BudgetTime.lean#L106-L116

import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSum_BudgetTime
set_option autoImplicit false
open ThreeSum ThreeSum.BudgetTime
open Filter Real ThreeSum.Parameters ThreeSum.StageBounds
  ThreeSum.UniformStageBounds
open scoped Topology
set_option maxHeartbeats 400000

theorem ThreeSum.BudgetTime.solvedInTime_of_program_contract (Q : EndStatement.Problem)
    (hprogram : ∀ κ : ℕ, ∃ (P : List EndStatement.Instr) (w : ℕ) (T : ℕ → ℕ)
      (a b C k : ℕ),
      (∀ᶠ n : ℕ in atTop, T n ≤ compiledBudget a b C k n) ∧
      ∀ (n : ℕ) (x : Q.Instance n),
        (∀ z ∈ Q.input x, z.natAbs ≤ n ^ κ) →
        ∀ W ≥ w * (Nat.log2 n + 1), Q.SolvedBy x P W (T n)) :
    Q.SolvedInTime (981 / 500) := by sorry
