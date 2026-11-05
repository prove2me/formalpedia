-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalMomentSourceProgram_positions_range
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentSourceProgram.positions_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:10:11.988512+00:00
-- url     : https://prove2.me/theorems/94c59b95-7ca7-40d2-a0d2-d91faf12ca06
-- title:
--   positions_range
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryMomentSourceProgram.lean#L55-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryMomentSourceProgram.lean#L55-L60

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountHost
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentSourceProgram
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentSourceProgram
open Light TernaryWeightChannels

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentSourceProgram.positions_range (arity : ℕ) (h : arity=115) :
    ∀ a∈positions, 9≤a ∧ a<arity := by sorry
