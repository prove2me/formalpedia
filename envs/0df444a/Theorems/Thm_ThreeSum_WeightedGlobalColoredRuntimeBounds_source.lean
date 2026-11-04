-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredRuntimeBounds_source
-- name    : ThreeSum.WeightedGlobalColoredRuntimeBounds.source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:31:40.928515+00:00
-- url     : https://prove2.me/theorems/ba394d81-11ad-409e-95dc-3a40f6b1824f
-- title:
--   Weighted Global Colored Runtime Bounds: source
-- statement:
--   Actual append outputs may have arbitrary repeated native keys; they do
--   not alter the counted source sizes or allocated coefficient bounds.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredRuntimeBounds.lean#L47-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredRuntimeBounds.lean#L47-L53

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedCollisions
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTimeMonotone
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeBounds
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredRuntimeBounds
open WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalArenaSourceSetup
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory WeightedGlobalLocalParameters
open WeightedGlobalActualColoredRuntime
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredRuntimeBounds.source (P : Profile κ) (I : Input) (A : Inputs) (n j seed : ℕ)
    (D : Data (config P.p j I A seed))
    (hj : j≤rounds P n) (hB : I.nB≤n) (hC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(J P n)) (hw : I.weightCap≤weight P n) :
    NativeBounds (k:=P.k) P.maps P.output (zeroInput (sourceInput I A seed D))
      n (n^κ) κ (2^(J P n)) (coefficient P) P.allocation.E j := by sorry
