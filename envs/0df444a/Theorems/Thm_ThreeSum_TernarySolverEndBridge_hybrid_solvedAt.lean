-- Prove2me | Theorems.Thm_ThreeSum_TernarySolverEndBridge_hybrid_solvedAt
-- name    : ThreeSum.TernarySolverEndBridge.hybrid_solvedAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:48:08.860615+00:00
-- url     : https://prove2.me/theorems/8ea8fc2b-dcc6-4026-b443-867c082b47b6
-- title:
--   Ternary Solver End Bridge: hybrid solved At
-- statement:
--   Exact public-model conclusion from the fully instantiated fast program.
--   Both the finite exceptional inputs and excessive magnitude branch execute
--   the original four-procedure triple scan.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySolverEndBridge.lean#L84-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySolverEndBridge.lean#L84-L90

import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySolverEndBridge
open Light Filter StageBounds
open scoped Topology
set_option maxHeartbeats 1500000
set_option maxRecDepth 16000

theorem ThreeSum.TernarySolverEndBridge.hybrid_solvedAt {P : Program} {p κ cutoff : ℕ}
    {T : ℕ→ ℕ} {need : ℕ→ ℕ→ Need} {a : ℝ}
    (hexec : FastExecution P p κ cutoff T need) (hp : PolyNeed need)
    (ht : PowerBound T a) (ha : 0≤ a) (hmargin : a<targetExponent) :
    ThreeSumApsp.WordRam.SolvedInTimeAt EndStatement.ThreeSum κ (4800698571997281331/2500000000000000000:ℝ) 0 := by sorry
