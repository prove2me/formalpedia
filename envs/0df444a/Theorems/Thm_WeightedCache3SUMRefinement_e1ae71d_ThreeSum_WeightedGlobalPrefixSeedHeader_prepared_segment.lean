-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPrefixSeedHeader_prepared_segment
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSeedHeader.prepared_segment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:13:57.016022+00:00
-- url     : https://prove2.me/theorems/a8146085-c58a-4e97-b5b1-01fc0fe288ea
-- title:
--   prepared_segment
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean#L37-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean#L37-L45

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixSeedHeader
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSeedHeader
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open LightWeightedGlobalPrefixStep LightWeightedGlobalPrefixHeader LightWeightedGlobalPrefixFinish
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSeedHeader.prepared_segment {X : Inputs} {μ ν : ℕ→ℤ} {xs : List ℤ}
    (H : Prepared X μ ν) (hs : Seg μ X.seed xs)
    (hbefore : X.seed+xs.length≤X.prefixFree) (hafter : X.liveHeader+106≤X.seed) :
    Seg ν X.seed (result xs X) := by sorry
