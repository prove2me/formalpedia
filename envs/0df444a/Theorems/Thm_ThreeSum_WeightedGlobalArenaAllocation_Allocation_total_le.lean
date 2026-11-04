-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaAllocation_Allocation_total_le
-- name    : ThreeSum.WeightedGlobalArenaAllocation.Allocation.total_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:04:50.218986+00:00
-- url     : https://prove2.me/theorems/569a3d2a-9533-4717-84e0-8bb8b39b0027
-- title:
--   Allocation: total le
-- statement:
--   The Allocation construction uses the total le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaAllocation.lean#L54-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaAllocation.lean#L54-L62

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocation
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaAllocation
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaLayout
open WeightedGlobalCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaAllocation.Allocation.total_le {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (A : Allocation maps τ cap M b K H drift scale) (n U j : ℕ)
    (hj : j≤Nat.clog M (n^2)) :
    total maps τ cap M b K H drift scale n U j≤capacity A.D A.E (n+U) := by sorry
