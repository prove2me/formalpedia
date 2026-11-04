-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredTerminalReceipt_collision_bounds
-- name    : ThreeSum.WeightedGlobalColoredTerminalReceipt.collision_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:21:07.947123+00:00
-- url     : https://prove2.me/theorems/1ef61e23-0082-45d4-865c-82b80f8fe52b
-- title:
--   Weighted Global Colored Terminal Receipt: collision bounds
-- statement:
--   The actual packed endpoint collision counts paid by final cleanup obey
--   its fixed exponent, including the literal selector's factor nine.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredTerminalReceipt.lean#L151-L162
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredTerminalReceipt.lean#L151-L162

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTerminalReceipt
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControlBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedCollisions
import Definitions.Def_Submission_Weighted_Global_TernaryColoredTerminalReceipt
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredTerminalReceipt
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalArenaSelectedSigned
open WeightedGlobalColoredLoopSetup LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]

theorem ThreeSum.WeightedGlobalColoredTerminalReceipt.collision_bounds (hmeta : WeightedGlobalPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : WeightedGlobalArenaFixedParameters.InputGuards P.K P.m P.radix κ n) :
    ((TernaryOriginalCollisions.collisionPairs (fun i : Fin B.length=>
      keysB P n free menu c A B C initial i.val)).card : ℝ)≤(n : ℝ)^(7483/10000 : ℝ) ∧
    ((TernaryOriginalCollisions.collisionPairs (fun i : Fin C.length=>
      keysC P n free menu c A B C initial i.val)).card : ℝ)≤(n : ℝ)^(7483/10000 : ℝ) := by sorry
