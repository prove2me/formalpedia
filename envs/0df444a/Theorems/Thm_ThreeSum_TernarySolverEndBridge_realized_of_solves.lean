-- Prove2me | Theorems.Thm_ThreeSum_TernarySolverEndBridge_realized_of_solves
-- name    : ThreeSum.TernarySolverEndBridge.realized_of_solves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:07:44.550197+00:00
-- url     : https://prove2.me/theorems/3cd6cd1c-faf8-4800-b4c2-fef9ca9a3248
-- title:
--   Ternary Solver End Bridge: realized of solves
-- statement:
--   The Ternary Solver End Bridge construction uses the realized of solves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySolverEndBridge.lean#L19-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySolverEndBridge.lean#L19-L22

import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Theorems.Thm_ThreeSum_TernaryEndBridge_realized_of_solves

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySolverEndBridge
open Light Filter StageBounds
open scoped Topology
set_option maxHeartbeats 1500000
set_option maxRecDepth 16000

theorem ThreeSum.TernarySolverEndBridge.realized_of_solves {P : Program} {p : ℕ} {T : ℕ→ ℕ→ ℕ} {need : ℕ→ ℕ→ Need}
    (hs : Solves s3Task P p T need) (hp : PolyNeed need) :
    ThreeSumApsp.WordRam.Realized EndStatement.ThreeSum (timeUpTo T) := by sorry
