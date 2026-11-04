-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopAllocationScalars_sum_word
-- name    : ThreeSum.WeightedGlobalColoredLoopAllocationScalars.sum_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:27:02.769499+00:00
-- url     : https://prove2.me/theorems/ae7773df-2d8e-4a81-b0b3-39bce5abc916
-- title:
--   Weighted Global Colored Loop Allocation Scalars: sum word
-- statement:
--   All constants and dimensions passed to the actual loop call are paid by
--   the initialized header/budget footprints, without independent scalar advice.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopAllocationScalars.lean#L25-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopAllocationScalars.lean#L25-L70

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocationScalars
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopAllocationScalars
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalColoredLoopAllocation
open WeightedGlobalArenaPrefixFootprints WeightedGlobalLocalParameters WeightedGlobalArenaLayout
set_option maxHeartbeats 200000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredLoopAllocationScalars.sum_word {lim : Limits} {depth : ℕ} (P : Profile κ) (n free : ℕ) (A B C : List ℤ)
    (hok : (WeightedGlobalArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free depth) :
    ((values P n).sum : ℤ)≤lim.word := by sorry
