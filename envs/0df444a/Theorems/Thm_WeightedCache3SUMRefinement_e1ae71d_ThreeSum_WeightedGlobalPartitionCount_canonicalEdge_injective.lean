-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPartitionCount_canonicalEdge_injective
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPartitionCount.canonicalEdge_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:20:38.770526+00:00
-- url     : https://prove2.me/theorems/4fa12ced-3123-4bf2-987f-cedfeb50e256
-- title:
--   canonicalEdge_injective
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPartitionCount.lean#L179-L185
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPartitionCount.lean#L179-L185

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalLocalParameters
import Mathlib.Tactic
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPartitionCount
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPartitionCount
open Finset TernaryJointType TernaryCoverLocal TernaryCoverRegularity TernaryCoverOutputCap
open TernaryTypeLowerBound

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPartitionCount.canonicalEdge_injective {t r s : ℕ} :
    Function.Injective (canonicalEdge (t := t) (r := r) (s := s)) := by sorry
