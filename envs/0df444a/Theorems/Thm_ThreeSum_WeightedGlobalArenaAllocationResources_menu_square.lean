-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaAllocationResources_menu_square
-- name    : ThreeSum.WeightedGlobalArenaAllocationResources.menu_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:09:38.822544+00:00
-- url     : https://prove2.me/theorems/68635ee4-85bf-4039-bd81-36b7ea609cdb
-- title:
--   Weighted Global Arena Allocation Resources: menu square
-- statement:
--   The Weighted Global Arena Allocation Resources construction uses the menu square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaAllocationResources.lean#L58-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaAllocationResources.lean#L58-L73

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaAllocationResources
open Light WeightedGlobalArenaLayout WeightedGlobalArenaAllocation
open WeightedGlobalCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaAllocationResources.menu_square {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (A : Allocation maps τ cap M b K H drift scale) (n U j : ℕ)
    (hj : j≤Nat.clog M (n^2)) :
    (p^(LightWeightedGlobalDimensions.dim M b p K n U))^2≤capacity A.D A.E (n+U) := by sorry
