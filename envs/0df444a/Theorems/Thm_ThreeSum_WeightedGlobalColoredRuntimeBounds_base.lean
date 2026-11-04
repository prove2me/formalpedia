-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredRuntimeBounds_base
-- name    : ThreeSum.WeightedGlobalColoredRuntimeBounds.base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:30:47.998594+00:00
-- url     : https://prove2.me/theorems/16cbb12f-2436-49b5-964e-aa335ac53284
-- title:
--   Weighted Global Colored Runtime Bounds: base
-- statement:
--   Every phase's allocated source dimensions and physical requester count
--   satisfy the native runtime model.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredRuntimeBounds.lean#L39-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredRuntimeBounds.lean#L39-L43

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

theorem ThreeSum.WeightedGlobalColoredRuntimeBounds.base (P : Profile κ) (n free j : ℕ) (A B C : List ℤ)
    (hj : j≤rounds P n) (hA : A.length≤n) (hB : B.length≤n) (hC : C.length≤n) :
    NativeBounds (k:=P.k) P.maps P.output (zeroInput (input P n free A B C))
      n (n^κ) κ (2^(J P n)) (coefficient P) P.allocation.E j := by sorry
