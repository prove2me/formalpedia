-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaAllocation_capacity_coefficient
-- name    : ThreeSum.WeightedGlobalArenaAllocation.capacity_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:05:09.421193+00:00
-- url     : https://prove2.me/theorems/a76b7746-1cd0-41e8-9814-c305246744f2
-- title:
--   Weighted Global Arena Allocation: capacity coefficient
-- statement:
--   The Weighted Global Arena Allocation construction uses the capacity coefficient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaAllocation.lean#L64-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaAllocation.lean#L64-L67

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocation
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaAllocation
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaLayout
open WeightedGlobalCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaAllocation.capacity_coefficient (D E x : ℕ) : 256*(D+1)≤capacity D E x := by sorry
