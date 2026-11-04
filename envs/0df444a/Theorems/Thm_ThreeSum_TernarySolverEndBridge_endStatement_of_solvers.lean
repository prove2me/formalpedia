-- Prove2me | Theorems.Thm_ThreeSum_TernarySolverEndBridge_endStatement_of_solvers
-- name    : ThreeSum.TernarySolverEndBridge.endStatement_of_solvers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:15:47.231204+00:00
-- url     : https://prove2.me/theorems/a9e91948-072a-4f5c-a110-1f807a203dd5
-- title:
--   Ternary Solver End Bridge: end Statement of solvers
-- statement:
--   The final publication theorem needs one real solver and resource/time
--   proof for every fixed original-input magnitude exponent.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySolverEndBridge.lean#L41-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySolverEndBridge.lean#L41-L47

import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Theorems.Thm_ThreeSum_TernaryEndBridge_endStatement_of_solvers

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySolverEndBridge
open Light Filter StageBounds
open scoped Topology
set_option maxHeartbeats 1500000
set_option maxRecDepth 16000

theorem ThreeSum.TernarySolverEndBridge.endStatement_of_solvers
    (h : ∀ κ : ℕ, ∃ (P : Program) (p : ℕ) (T : ℕ→ ℕ→ ℕ) (need : ℕ→ ℕ→ Need),
      Solves s3Task P p T need ∧ PolyNeed need ∧
      ∀ᶠ n : ℕ in atTop, timeUpTo T n ((n:ℝ)^(κ:ℝ))≤ (n:ℝ)^targetExponent) :
    EndStatement.ThreeSum.SolvedInTime (4800698571997281331/2500000000000000000:Rat) := by sorry
