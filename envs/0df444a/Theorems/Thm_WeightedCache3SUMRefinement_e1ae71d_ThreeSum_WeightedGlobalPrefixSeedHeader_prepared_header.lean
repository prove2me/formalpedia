-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPrefixSeedHeader_prepared_header
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSeedHeader.prepared_header
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:14:29.65681+00:00
-- url     : https://prove2.me/theorems/34df7ba0-d061-4d4d-b083-6dc26cd2038b
-- title:
--   prepared_header
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean#L62-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean#L62-L69

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSeedHeader.prepared_header {X : Inputs} {C : Config} {μ ν : ℕ→ℤ}
    {n dB dC dP tB tC tP newSpan : ℕ}
    (H : Prepared X μ ν) (hs : Seg μ X.seed (header C n dB dC dP tB tC tP newSpan))
    (hbefore : X.seed+48≤X.prefixFree) (hafter : X.liveHeader+106≤X.seed) :
    Seg ν X.seed (header (nextConfig C X) n (X.xB*X.p) (X.xC*X.p) (X.xP*X.a)
      (X.tB*9) (X.tC*9) (X.tP*X.b*X.scale) newSpan) := by sorry
