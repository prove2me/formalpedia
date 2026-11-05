-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaAllocation_Allocation_total_le
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaAllocation.Allocation.total_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T14:26:52.623177+00:00
-- url     : https://prove2.me/theorems/7f8435e9-a5b5-4185-a9bb-3c3d2af8d1c0
-- title:
--   total_le
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaAllocation.lean#L54-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaAllocation.lean#L54-L62

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaAllocation
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaAllocation
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaLayout
open WeightedGlobalCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaAllocation.Allocation.total_le {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (A : Allocation maps τ cap M b K H drift scale) (n U j : ℕ)
    (hj : j≤Nat.clog M (n^2)) :
    total maps τ cap M b K H drift scale n U j≤capacity A.D A.E (n+U) := by sorry
