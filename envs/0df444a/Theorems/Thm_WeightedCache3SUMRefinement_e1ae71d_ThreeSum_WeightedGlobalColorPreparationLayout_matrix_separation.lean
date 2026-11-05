-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColorPreparationLayout_matrix_separation
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout.matrix_separation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:49:41.716623+00:00
-- url     : https://prove2.me/theorems/5ee159b0-4c36-4956-8fee-f2eb81e6523d
-- title:
--   matrix_separation
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColorPreparationLayout.lean#L34-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColorPreparationLayout.lean#L34-L39

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColorPreparation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColorPreparationLayout
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout
open LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout.matrix_separation (free n W nA nB nC J : ℕ) :
    bMatrix free n W+nB*(J+2)=cMatrix free n W nB J ∧
    cMatrix free n W nB J+nC*(J+2)=carry free n W nA nB nC J ∧
    carry free n W nA nB nC J+2^J*(J+1)=positions free n W nA nB nC J ∧
    positions free n W nA nB nC J+nA*2^J=oMatrix free n W nA nB nC J := by sorry
