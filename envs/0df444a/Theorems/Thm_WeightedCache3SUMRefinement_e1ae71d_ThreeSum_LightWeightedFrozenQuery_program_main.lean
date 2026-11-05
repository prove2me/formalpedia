-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_program_main
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.program_main
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:53.181976+00:00
-- url     : https://prove2.me/theorems/fd86fccb-d252-41f1-9d79-819299576b80
-- title:
--   program_main
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Frozen.lean#L61-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Frozen.lean#L61-L61

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Frozen
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery
open Light

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.program_main : program[0]? = some (body 0 1 3 4 5) := by sorry
