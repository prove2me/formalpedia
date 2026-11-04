-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopSetup_right_injective
-- name    : ThreeSum.WeightedGlobalColoredLoopSetup.right_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:10:56.756064+00:00
-- url     : https://prove2.me/theorems/bb28a858-e87b-474d-86a4-f0cf0c77c61c
-- title:
--   Weighted Global Colored Loop Setup: right injective
-- statement:
--   The Weighted Global Colored Loop Setup construction uses the right injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopSetup.lean#L128-L134
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopSetup.lean#L128-L134

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepareAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Theorems.Thm_ThreeSum_WeightedGlobalSignedFeatureHash_right_injective

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopSetup
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (μ : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]

theorem ThreeSum.WeightedGlobalColoredLoopSetup.right_injective (hmeta : WeightedGlobalPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : WeightedGlobalArenaFixedParameters.InputGuards P.K P.m P.radix κ n) :
    Function.Injective (fun i : Fin C.length=>fun t : Fin (J P n+2)=>
      (WeightedGlobalArenaSelectedSigned.right (n^κ) P.radix (J P n) (fun j=>C.getD j 0) i.val t.val:ZMod P.p)) := by sorry
