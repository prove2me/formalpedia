-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPartitionCount_fixed_edge_mass_lower
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPartitionCount.fixed_edge_mass_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:20:32.598198+00:00
-- url     : https://prove2.me/theorems/0d42a231-81dd-477e-a2a2-c011022fd2b9
-- title:
--   fixed_edge_mass_lower
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPartitionCount.lean#L269-L285
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPartitionCount.lean#L269-L285

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
open WeightedGlobalLocalParameters

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPartitionCount.fixed_edge_mass_lower (m : ℕ) :
    (vertices (fixedLength m) (fixedPi m)).card*(2^(fixedPi m 1)*3^(fixedPi m 2)) ≤
    partitionLoss (2379766416784020*m) (292929977780940*m)*
      Fintype.card (LocalEdge (fixedLength m) (fixedAlpha m) (fixedPi m)) := by sorry
