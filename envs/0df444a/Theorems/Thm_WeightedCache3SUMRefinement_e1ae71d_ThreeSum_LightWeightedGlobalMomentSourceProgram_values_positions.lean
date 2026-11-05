-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalMomentSourceProgram_values_positions
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentSourceProgram.values_positions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:10:08.111821+00:00
-- url     : https://prove2.me/theorems/cb8d5f11-87c3-441d-9d7a-44f962869840
-- title:
--   values_positions
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryMomentSourceProgram.lean#L64-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryMomentSourceProgram.lean#L64-L77

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentSourceProgram.values_positions (originalB nB originalC nC leftWeight rightWeight matrix count out : ℕ)
    (backend : List ℤ) (hlen : backend.length=106) :
    LightTernaryMomentChannelStep.values positions
      (LightTernaryMomentChannelStep.args originalB nB originalC nC
        leftWeight rightWeight matrix count out backend)=backend := by sorry
