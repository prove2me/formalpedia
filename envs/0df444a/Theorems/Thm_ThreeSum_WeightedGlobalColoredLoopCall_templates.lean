-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopCall_templates
-- name    : ThreeSum.WeightedGlobalColoredLoopCall.templates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:46:31.295557+00:00
-- url     : https://prove2.me/theorems/00ea5479-bdbb-4065-b3d6-3e2adb2aa47f
-- title:
--   Weighted Global Colored Loop Call: templates
-- statement:
--   The genuine initializer's two template segments are exactly those
--   consumed by the actual prefix initializer, including its computed budgets.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopCall.lean#L33-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopCall.lean#L33-L64

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSeedABI
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopABI
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopReady
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocationScalars
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopCall
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLoop_Ready_start
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixState_start
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopCall
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open LightWeightedGlobalColoredInitializationProof
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]

theorem ThreeSum.WeightedGlobalColoredLoopCall.templates {loc start : ℕ→ℤ} {μ : ℕ→ℤ}
    (HI : Initialized P.allocation.D P.allocation.E P.K P.radix (P.p^(2*P.K)) P.drift P.scale
      n (n^κ) (input P n free A B C).free (q P n) (J P n) (A.length*2^(J P n))
      (initValues P n free menu A B C) start loc initial μ) :
    let S:=setup P n free menu c A B C initial
    Seg μ (addr S.input.free S.input.capacity 0)
      (WeightedGlobalArenaHeaderAgreement.templateValues S.input P.p P.m P.F) ∧
    Seg μ (addr S.input.free S.input.capacity 2) (S.seedHeader 0) := by sorry
