-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopAllocation_beta_eq_drift
-- name    : ThreeSum.WeightedGlobalColoredLoopAllocation.beta_eq_drift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:31:38.977606+00:00
-- url     : https://prove2.me/theorems/c2eb6839-6843-4625-a3bb-8eba60335d7d
-- title:
--   Weighted Global Colored Loop Allocation: beta eq drift
-- statement:
--   The mathematical selector's drift is exactly the compiled integer
--   constant, including every local map occurrence and output word.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopAllocation.lean#L21-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopAllocation.lean#L21-L25

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopAllocation
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalArenaPrefixFootprints
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredLoopAllocation.beta_eq_drift (P : Profile κ) :
    9*WeightedGlobalArenaBudgetExistence.pairFactor P.m P.F P.K=P.drift := by sorry
