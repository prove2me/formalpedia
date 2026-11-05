-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalGlobalPreludeResources_need_poly
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalPreludeResources.need_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:47:15.351645+00:00
-- url     : https://prove2.me/theorems/337dad1e-1090-4be0-88ca-847bf7162e49
-- title:
--   need_poly
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryGlobalPreludeResources.lean#L113-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryGlobalPreludeResources.lean#L113-L123

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryGlobalPreludeProof
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensionsBudget
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGlobalPreludeResources
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalPreludeResources
open Light LightWeightedGlobalGlobalPrelude
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalPreludeResources.need_poly {M b p K : ℕ} [Fact p.Prime] (hM : 1<M) (hb : 1<b) (κ : ℕ) :
    PolyNeed (need M b p K κ) := by sorry
