-- Prove2me | Theorems.Thm_ThreeSum_TernarySolverEndBridge_hybrid_timeUpTo
-- name    : ThreeSum.TernarySolverEndBridge.hybrid_timeUpTo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:47:22.65469+00:00
-- url     : https://prove2.me/theorems/28e9615d-8d3a-4b72-b76f-3ec79e471877
-- title:
--   Ternary Solver End Bridge: hybrid time Up To
-- statement:
--   The Ternary Solver End Bridge construction uses the hybrid time Up To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySolverEndBridge.lean#L75-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySolverEndBridge.lean#L75-L79

import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySolverEndBridge
open Light Filter StageBounds
open scoped Topology
set_option maxHeartbeats 1500000
set_option maxRecDepth 16000

theorem ThreeSum.TernarySolverEndBridge.hybrid_timeUpTo {T : ℕ→ ℕ} {a : ℝ}
    (ht : PowerBound T a) (ha : 0≤ a) (hmargin : a<targetExponent) (κ cutoff : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      timeUpTo (TernaryHybridCore.time T κ cutoff) n ((n:ℝ)^(κ:ℝ))≤ (n:ℝ)^targetExponent := by sorry
