-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaCapacity_polyBound_le_capacity
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCapacity.polyBound_le_capacity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:29:08.964521+00:00
-- url     : https://prove2.me/theorems/7d67784f-127a-4121-9837-e4f625ce51ca
-- title:
--   polyBound_le_capacity
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaCapacity.lean#L16-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaCapacity.lean#L16-L25

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCapacity
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCapacity
open Light WeightedGlobalArenaLayout

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCapacity.polyBound_le_capacity (s k n U : ℕ) :
    polyBound s k [n,U]≤capacity (2^s) (2*k) (n+U) := by sorry
