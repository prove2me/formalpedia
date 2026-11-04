-- Prove2me | Theorems.Thm_ThreeSum_TernarySolverEndBridge_solvedAt_of_solves
-- name    : ThreeSum.TernarySolverEndBridge.solvedAt_of_solves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:11:24.764208+00:00
-- url     : https://prove2.me/theorems/dcfe256e-5368-48e9-b514-484774359202
-- title:
--   Ternary Solver End Bridge: solved At of solves
-- statement:
--   The Ternary Solver End Bridge construction uses the solved At of solves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySolverEndBridge.lean#L24-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySolverEndBridge.lean#L24-L30

import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Theorems.Thm_ThreeSum_TernaryEndBridge_solvedAt_of_solves

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySolverEndBridge
open Light Filter StageBounds
open scoped Topology
set_option maxHeartbeats 1500000
set_option maxRecDepth 16000

theorem ThreeSum.TernarySolverEndBridge.solvedAt_of_solves {κ : ℕ} {P : Program} {p : ℕ}
    {T : ℕ→ ℕ→ ℕ} {need : ℕ→ ℕ→ Need}
    (hs : Solves s3Task P p T need) (hp : PolyNeed need)
    (ht : ∀ᶠ n : ℕ in atTop,
      timeUpTo T n ((n:ℝ)^(κ:ℝ))≤ (n:ℝ)^targetExponent) :
    ThreeSumApsp.WordRam.SolvedInTimeAt EndStatement.ThreeSum κ (4800698571997281331/2500000000000000000:ℝ) 0 := by sorry
