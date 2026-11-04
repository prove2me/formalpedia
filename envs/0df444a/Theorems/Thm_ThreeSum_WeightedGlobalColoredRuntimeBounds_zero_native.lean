-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredRuntimeBounds_zero_native
-- name    : ThreeSum.WeightedGlobalColoredRuntimeBounds.zero_native
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:28:08.049383+00:00
-- url     : https://prove2.me/theorems/582e2a5f-86c3-4dc1-8246-1a2e8fb95886
-- title:
--   Weighted Global Colored Runtime Bounds: zero native
-- statement:
--   Zero-query analysis retains all actual source keys and requester rows.
--   Only the separately charged query-time field is reset.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredRuntimeBounds.lean#L29-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredRuntimeBounds.lean#L29-L35

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedCollisions
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTimeMonotone
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeBounds
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredRuntimeBounds
open WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalArenaSourceSetup
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory WeightedGlobalLocalParameters
open WeightedGlobalActualColoredRuntime
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredRuntimeBounds.zero_native (P : Profile κ) (I : Input) (n j : ℕ)
    (hj : j≤rounds P n) (hB : I.nB≤n) (hC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(J P n)) (hw : I.weightCap≤weight P n) :
    NativeBounds (k:=P.k) P.maps P.output (zeroInput I)
      n (n^κ) κ (2^(J P n)) (coefficient P) P.allocation.E j := by sorry
