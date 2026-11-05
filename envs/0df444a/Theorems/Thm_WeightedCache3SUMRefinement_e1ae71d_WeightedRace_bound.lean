-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedRace_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.WeightedRace.bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:19:34.303314+00:00
-- url     : https://prove2.me/theorems/12344b80-505e-420a-a481-f64fda2e435f
-- title:
--   bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted.lean#L7-L8
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted.lean#L7-L8

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFinalSolver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaQueryTime_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceValues_bound

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open WeightedCache3SUMRefinement_e1ae71d.WeightedRace

theorem WeightedCache3SUMRefinement_e1ae71d.WeightedRace.bound : EndStatement.ThreeSum.SolvedInTime (384055881637/200000000000 : Rat) := by sorry
