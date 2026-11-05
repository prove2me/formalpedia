-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_projection_fiber_log_choose_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters.projection_fiber_log_choose_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:17.143578+00:00
-- url     : https://prove2.me/theorems/e0e56836-0431-4de4-8a49-e60e9a8acaed
-- title:
--   projection_fiber_log_choose_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalParameters.lean#L140-L161
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalParameters.lean#L140-L161

import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters.projection_fiber_log_choose_bound {m : ℕ} (hm : 0 < m) :
    Real.log (((30000000000000000 * m).choose (292929977780940 * m) : ℕ) : ℝ) <
      (30000000000000000 * m : ℕ) * Real.log 2 / 4 := by sorry
