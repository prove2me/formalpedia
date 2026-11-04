-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopAllocationScalars_member_word
-- name    : ThreeSum.WeightedGlobalColoredLoopAllocationScalars.member_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:30:49.303397+00:00
-- url     : https://prove2.me/theorems/9c4b132d-5666-4845-bc2e-875adfb9efc4
-- title:
--   Weighted Global Colored Loop Allocation Scalars: member word
-- statement:
--   The Weighted Global Colored Loop Allocation Scalars construction uses the member word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopAllocationScalars.lean#L72-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopAllocationScalars.lean#L72-L80

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

theorem ThreeSum.WeightedGlobalColoredLoopAllocationScalars.member_word {lim : Limits} {depth : ℕ} (P : Profile κ) (n free : ℕ) (A B C : List ℤ)
    (hok : (WeightedGlobalArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free depth) :
    ∀z∈values P n, |(z : ℤ)|≤lim.word := by sorry
