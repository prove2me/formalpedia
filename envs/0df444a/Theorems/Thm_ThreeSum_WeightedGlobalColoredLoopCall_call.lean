-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopCall_call
-- name    : ThreeSum.WeightedGlobalColoredLoopCall.call
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:41:48.66565+00:00
-- url     : https://prove2.me/theorems/d1325d3e-7385-4838-80ad-d515d7f8ae60
-- title:
--   Weighted Global Colored Loop Call: call
-- statement:
--   Actual call237 from the physical initialization output. No template,
--   initial-key, span, loop or kernel execution is assumed as advice.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopCall.lean#L97-L147
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopCall.lean#L97-L147

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSeedABI
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopABI
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopReady
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocationScalars
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopCall
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLoop_Ready_start
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
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

theorem ThreeSum.WeightedGlobalColoredLoopCall.call {lim : Limits} {d header : ℕ} (start loc μ : ℕ→ℤ)
    (HI : Initialized P.allocation.D P.allocation.E P.K P.radix (P.p^(2*P.K)) P.drift P.scale
      n (n^κ) (input P n free A B C).free (q P n) (J P n) (A.length*2^(J P n))
      (initValues P n free menu A B C) start loc initial μ)
    (HR : WeightedGlobalArenaLoop.Ready (setup P n free menu c A B C initial) lim (d+2))
    (h5 : loc 5=(header:ℤ))
    (hR : μ (header+15)=(rounds P n:ℤ)) (hJ : μ (header+16)=(J P n:ℤ))
    (hheader : header+17≤lim.space) :
    let S:=setup P n free menu c A B C initial
    Ends lim P.color d
      (.call 249 (LightWeightedGlobalColoredSolver.loopArgs P.m P.F P.p (fixedAlpha P.m 2) (alphaRank P.m)
        (TernaryCodeSemantics.address P.output.val) (4^fixedLength P.m) (P.p^(2*P.K)) P.drift P.scale) 12)
      ⟨loc,μ⟩ (25+S.initTime)
      (fun σ=>σ.loc 12=((P.p^(rounds P n):ℕ):ℤ) ∧
        WeightedGlobalArenaLoop.Invariant S S.rounds σ.mem ∧ ∀i,i≠12→σ.loc i=loc i) := by sorry
