-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_program_erase
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.program_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:07:06.532146+00:00
-- url     : https://prove2.me/theorems/644f8a41-b953-4eaa-9d4a-1b43d08f0cc1
-- title:
--   program_erase
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Frozen.lean#L66-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Frozen.lean#L66-L66

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Frozen
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery
open Light

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.program_erase : program[5]? = some (LightMaskErase.body 5) := by sorry
