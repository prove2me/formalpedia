-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopAllocation_control_words
-- name    : ThreeSum.WeightedGlobalColoredLoopAllocation.control_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:19:22.506452+00:00
-- url     : https://prove2.me/theorems/4b0bfc01-61c9-428b-bd27-9c428aa71e01
-- title:
--   Weighted Global Colored Loop Allocation: control words
-- statement:
--   Round and radix-power words come from the same universal allocation;
--   no independently supplied hardware bounds remain.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopAllocation.lean#L77-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopAllocation.lean#L77-L94

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

theorem ThreeSum.WeightedGlobalColoredLoopAllocation.control_words {lim : Limits} {depth : ℕ}
    (P : Profile κ) (n free : ℕ) (A B C : List ℤ)
    (hok : (WeightedGlobalArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free depth) :
    (rounds P n : ℤ)≤lim.word ∧
      ∀j≤rounds P n, ((P.p^j : ℕ):ℤ)≤lim.word := by sorry
