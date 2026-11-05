-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaCapacity_exists_capacity
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCapacity.exists_capacity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:29:14.128393+00:00
-- url     : https://prove2.me/theorems/e3a6f8d6-e3b1-47f9-ba7e-bae51201fd4d
-- title:
--   exists_capacity
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaCapacity.lean#L27-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaCapacity.lean#L27-L36

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCapacity
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCapacity
open Light WeightedGlobalArenaLayout

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCapacity.exists_capacity {need : ℕ→ℕ→Need} (h : PolyNeed need) :
    ∃ D E : ℕ, ∀ n U,
      (need n U).word≤capacity D E (n+U) ∧
      (need n U).cells≤capacity D E (n+U) ∧
      (need n U).depth≤capacity D E (n+U) := by sorry
