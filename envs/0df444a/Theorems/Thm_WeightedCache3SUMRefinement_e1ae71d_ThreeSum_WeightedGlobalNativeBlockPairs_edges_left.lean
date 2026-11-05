-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeBlockPairs_edges_left
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeBlockPairs.edges_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:51:41.384727+00:00
-- url     : https://prove2.me/theorems/c69a9d09-ef58-4654-9e15-85d6a73ffd1d
-- title:
--   edges_left
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeBlockPairs.lean#L72-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeBlockPairs.lean#L72-L73

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryRepeatedWords
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPhysicalTupleRecords
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeBlockPairs
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeBlockPairs
open Finset TernaryJointType TernaryCoverLocal WeightedGlobalRepeatedWords
attribute [local instance] Classical.propDecidable
variable {r L F : ℕ} {α π : DigitType}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeBlockPairs.edges_left (a b : Fin r→{w // w∈vertices L α})
    (q : Fin r→{w // w∈vertices L π}) (h) (i : Fin r) : left (edges a b q h i)=(a i).val := by sorry

attribute [defeq] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeBlockPairs.edges_left
