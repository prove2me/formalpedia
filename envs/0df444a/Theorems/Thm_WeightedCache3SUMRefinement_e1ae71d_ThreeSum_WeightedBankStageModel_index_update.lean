-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankStageModel_index_update
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankStageModel.index_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:10:23.871306+00:00
-- url     : https://prove2.me/theorems/9399d7df-f15d-4c41-9ded-2047b80e16cd
-- title:
--   index_update
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankStageModel.lean#L60-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankStageModel.lean#L60-L63

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankStageModel
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankStageModel.index_update {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (e : Fin 3) (j : ℕ) (hj : j<n) (he : e≤E.word j i) :
    E.word (index E i e j)=Function.update (E.word j) i e := by sorry
