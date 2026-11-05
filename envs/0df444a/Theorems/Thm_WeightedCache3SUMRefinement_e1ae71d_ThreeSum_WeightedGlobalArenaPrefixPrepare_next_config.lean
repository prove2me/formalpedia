-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPrefixPrepare_next_config
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixPrepare.next_config
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:24:13.930654+00:00
-- url     : https://prove2.me/theorems/08d84333-0793-4786-a2b8-9341735d5489
-- title:
--   next_config
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPrefixPrepare.lean#L196-L202
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPrefixPrepare.lean#L196-L202

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixPrepare
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixPrepare
open Light WeightedGlobalLocalParameters TernaryJointType WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup
open LightWeightedGlobalPrefixStep
set_option maxHeartbeats 1000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixPrepare.next_config (p m F j J n U0 a b scale : ℕ) (I : Input)
    (A : WeightedGlobalArenaSeedCandidate.Inputs) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (hJ : J=A.J) :
    WeightedGlobalPrefixSeedHeader.nextConfig (WeightedGlobalArenaSeedCandidate.config p j I A 0)
      (inputs p m F j J n U0 a b scale I Q)=WeightedGlobalArenaSeedCandidate.config p (j+1) I A 0 := by sorry
