-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredRuntimeBounds_selected
-- name    : ThreeSum.WeightedGlobalColoredRuntimeBounds.selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:27:46.138576+00:00
-- url     : https://prove2.me/theorems/b5185bdb-826c-42db-9645-e5540b6b65d6
-- title:
--   Weighted Global Colored Runtime Bounds: selected
-- statement:
--   Runtime source bounds remain valid after actual singleton compaction
--   and the exact selected-hash re-encoding of the original values.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredRuntimeBounds.lean#L57-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredRuntimeBounds.lean#L57-L69

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedCollisions
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTimeMonotone
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeBounds
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_selected
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedCollisions_selected

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredRuntimeBounds
open WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalArenaSourceSetup
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory WeightedGlobalLocalParameters
open WeightedGlobalActualColoredRuntime
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredRuntimeBounds.selected (P : Profile κ) (n free j : ℕ) (A B C : List ℤ)
    (H : (TernarySignedReduction.Coordinate (J P n)→ZMod P.p)→ₗ[ZMod P.p] (Fin j→ZMod P.p))
    (valuesA valuesB valuesC : ℕ→ℤ) (keysB keysC : ℕ→ℕ)
    (hj : j≤rounds P n) (hA : A.length≤n) (hB : B.length≤n) (hC : C.length≤n) :
    NativeBounds (k:=P.k) P.maps P.output
      (zeroInput (WeightedGlobalArenaPostSelection.selectedInput (input P n free A B C)
        (n^κ) P.radix A.length H valuesA valuesB valuesC keysB keysC))
      n (n^κ) κ (2^(J P n)) (coefficient P) P.allocation.E j := by sorry
