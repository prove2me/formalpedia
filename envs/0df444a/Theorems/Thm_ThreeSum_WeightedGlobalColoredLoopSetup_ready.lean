-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopSetup_ready
-- name    : ThreeSum.WeightedGlobalColoredLoopSetup.ready
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:34:44.161324+00:00
-- url     : https://prove2.me/theorems/a3687496-3867-4993-99ff-81cc6fcce31b
-- title:
--   Weighted Global Colored Loop Setup: ready
-- statement:
--   Concrete readiness from actual preprocessing reads and fixed profile
--   mathematics. No phase execution or selected-row oracle is assumed.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopReady.lean#L22-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopReady.lean#L22-L95

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoop
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopReady
import Theorems.Thm_ThreeSum_LightTernaryQueryPlan_ready
import Theorems.Thm_ThreeSum_LightWeightedQueryPlan_ready
import Theorems.Thm_ThreeSum_WeightedGlobalArenaCountReady_ready
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixInputs_ready
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixPrepare_ready
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedScoreReady_ready
import Theorems.Thm_ThreeSum_WeightedGlobalArenaTensorReady_ready

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopSetup
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalArenaSelectedSigned
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredLoopSetup.ready (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (μ : ℕ→ℤ)
    [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
    {lim : Limits} {depth : ℕ}
    (hw : (WeightedGlobalArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free (depth+2))
    (hmeta : WeightedGlobalPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : WeightedGlobalArenaFixedParameters.InputGuards P.K P.m P.radix κ n)
    (horiginal : WeightedGlobalArenaPrefixInputs.Originals (input P n free A B C) (arrays P n free menu A B C)
      (q P n*q P n) P.radix P.radix n
      (WeightedGlobalComputedExtensionMenu.functional (p:=P.p) (c:=c) (dim_pos P n))
      (WeightedGlobalArenaFamilyBudget.seedAt (WeightedGlobalComputedExtensionMenu.seeds (p:=P.p) (d:=dim P n) (c:=c)))
      (left (n^κ) P.radix (J P n) (fun i=>B.getD i 0))
      (right (n^κ) P.radix (J P n) (fun i=>C.getD i 0))
      (requester (n^κ) P.radix (J P n) (fun i=>A.getD i 0)) μ) :
    WeightedGlobalArenaLoop.Ready (setup P n free menu c A B C μ) lim depth := by sorry
