-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColorPreparationLayout_matrices_before_work
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout.matrices_before_work
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:54:32.597554+00:00
-- url     : https://prove2.me/theorems/24d1e9a1-3120-45cd-afa5-a51598b36fed
-- title:
--   matrices_before_work
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColorPreparationLayout.lean#L25-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColorPreparationLayout.lean#L25-L32

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColorPreparation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColorPreparationLayout
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout
open LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout.matrices_before_work (free n W nA nB nC J : ℕ) :
    bMatrix free n W+nB*(J+2)≤work free n W nA nB nC J ∧
    cMatrix free n W nB J+nC*(J+2)≤work free n W nA nB nC J ∧
    oMatrix free n W nA nB nC J+nA*2^J*(J+2)≤work free n W nA nB nC J ∧
    positions free n W nA nB nC J+nA*2^J≤work free n W nA nB nC J ∧
    carry free n W nA nB nC J+2^J*(J+1)≤work free n W nA nB nC J := by sorry
