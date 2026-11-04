-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredTerminalReceipt_metadata_ends
-- name    : ThreeSum.WeightedGlobalColoredTerminalReceipt.metadata_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:35:56.645472+00:00
-- url     : https://prove2.me/theorems/ffc7cfb0-3ec8-41e8-a912-9ac50b7168c6
-- title:
--   Weighted Global Colored Terminal Receipt: metadata ends
-- statement:
--   The two retained metadata windows fit inside the literal arena.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredTerminalReceipt.lean#L71-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredTerminalReceipt.lean#L71-L92

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTerminalReceipt
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControlBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedCollisions
import Definitions.Def_Submission_Weighted_Global_TernaryColoredTerminalReceipt
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
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

theorem ThreeSum.WeightedGlobalColoredTerminalReceipt.metadata_ends :
    let I:=input P n free A B C
    I.prefixFree+nb P.m (rounds P n)≤addr I.free I.capacity 16 ∧
    I.prefixFree+4^(WeightedGlobalArenaSourceSetup.N P.m (rounds P n))+
      (2*WeightedGlobalArenaSourceSetup.N P.m (rounds P n)+1)≤addr I.free I.capacity 16 := by sorry
