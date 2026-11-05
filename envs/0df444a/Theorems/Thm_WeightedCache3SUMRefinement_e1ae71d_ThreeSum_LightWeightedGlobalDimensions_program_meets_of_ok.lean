-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalDimensions_program_meets_of_ok
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalDimensions.program_meets_of_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:37:31.956216+00:00
-- url     : https://prove2.me/theorems/ec5cc0d6-3f85-4acb-afff-4dab187c0870
-- title:
--   program_meets_of_ok
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryDimensionsBudget.lean#L108-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryDimensionsBudget.lean#L108-L116

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensionsBudget
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalDimensions
open Light WeightedGlobalSignedPadding TernaryExtensionEncoding
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalDimensions.program_meets_of_ok {lim : Limits} {M b p K n U dst depth : ℕ} [Fact p.Prime]
    (μ : ℕ → ℤ) (hM : 1<M) (hb : 1<b) (hn : 0<n)
    (hok : (need M b p K n U).Ok lim dst depth) :
    Meets lim (program M b p K) 0 depth [n,U,dst] μ (time M b p K n U)
      (fun z ν => z=((p^(dim M b p K n U) : ℕ) : ℤ) ∧
        Seg ν dst [(r M n : ℤ),J M b n U,dim M b p K n U,(p^(dim M b p K n U) : ℕ)] ∧
        Kept μ ν dst) := by sorry
