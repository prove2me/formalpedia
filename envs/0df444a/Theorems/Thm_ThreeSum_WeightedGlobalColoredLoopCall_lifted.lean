-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopCall_lifted
-- name    : ThreeSum.WeightedGlobalColoredLoopCall.lifted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:44:25.212684+00:00
-- url     : https://prove2.me/theorems/09147904-1b9b-43cc-b043-a1c9dd6df04e
-- title:
--   Weighted Global Colored Loop Call: lifted
-- statement:
--   The real entry182 receipt is relocated into procedure237 of the exact
--   compiled color executable.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopCall.lean#L68-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopCall.lean#L68-L93

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSeedABI
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopABI
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopReady
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocationScalars
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopCall
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
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ → ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]

theorem ThreeSum.WeightedGlobalColoredLoopCall.lifted {lim : Limits} {d : ℕ} (μ : ℕ → ℤ)
    (HR : WeightedGlobalArenaLoop.Ready (setup P n free menu c A B C initial) lim (d + 2))
    (hk : Kept initial μ (input P n free A B C).free)
    (ht :
      Seg μ (addr (input P n free A B C).free (cells P n) 0)
        (WeightedGlobalArenaHeaderAgreement.templateValues (input P n free A B C) P.p P.m P.F))
    (hs : Seg μ (addr (input P n free A B C).free (cells P n) 2) ((setup P n free menu c A B C initial).seedHeader 0)) :
    let S := setup P n free menu c A B C initial
    Meets lim P.color 249 (d + 1) S.initArgs μ S.initTime
      (fun z ν => z = ((P.p ^ (rounds P n) : ℕ) : ℤ) ∧ WeightedGlobalArenaLoop.Invariant S S.rounds ν) := by sorry
