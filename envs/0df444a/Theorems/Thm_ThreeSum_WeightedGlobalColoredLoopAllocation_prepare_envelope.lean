-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopAllocation_prepare_envelope
-- name    : ThreeSum.WeightedGlobalColoredLoopAllocation.prepare_envelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:19:18.138768+00:00
-- url     : https://prove2.me/theorems/89660215-4d42-44c3-b301-43e60d34569c
-- title:
--   Weighted Global Colored Loop Allocation: prepare envelope
-- statement:
--   Exact preparation-envelope arithmetic at every actual positive prefix.
--   The paired budget is the value written by the real initializer.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopAllocation.lean#L39-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopAllocation.lean#L39-L53

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopAllocation
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalArenaPrefixFootprints
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredLoopAllocation.prepare_envelope (P : Profile κ) (n free : ℕ) (A B C : List ℤ)
    (hA : A.length≤n) (j : ℕ) (hj : j<rounds P n) :
    WeightedGlobalArenaPrefixPrepare.envelope
      (WeightedGlobalArenaPrefixPrepare.inputs P.p P.m P.F j (J P n) n (initialBudget P n A)
        (P.p^(2*P.K)) (9*WeightedGlobalArenaBudgetExistence.pairFactor P.m P.F P.K)
        (2^(fixedPi P.m 2*P.K)) (input P n free A B C) P.output)≤
      (input P n free A B C).capacity := by sorry
