-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixHeader_headerWrites_good
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixHeader.headerWrites_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:03:45.309339+00:00
-- url     : https://prove2.me/theorems/5439b374-d999-4adb-8dbb-1d478baaa9f4
-- title:
--   headerWrites_good
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixHeader.lean#L75-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixHeader.lean#L75-L75

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixLoop
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixHeader
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixHeader
open Light
open LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixHeader.headerWrites_good : ∀ir∈headerWrites, ir.1<106 ∧ ir.2<30 := by sorry
