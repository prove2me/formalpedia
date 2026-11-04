-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixPrepare_next_config
-- name    : ThreeSum.WeightedGlobalArenaPrefixPrepare.next_config
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:17:37.849561+00:00
-- url     : https://prove2.me/theorems/3a50a549-46b4-4dbe-8e4b-69f38db8b415
-- title:
--   Weighted Global Arena Prefix Prepare: next config
-- statement:
--   The Weighted Global Arena Prefix Prepare construction uses the next config property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPrepare.lean#L196-L202
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPrepare.lean#L196-L202

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepare
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixPrepare
open Light WeightedGlobalLocalParameters TernaryJointType WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup
open LightWeightedGlobalPrefixStep
set_option maxHeartbeats 1000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaPrefixPrepare.next_config (p m F j J n U0 a b scale : ℕ) (I : Input)
    (A : WeightedGlobalArenaSeedCandidate.Inputs) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (hJ : J=A.J) :
    WeightedGlobalPrefixSeedHeader.nextConfig (WeightedGlobalArenaSeedCandidate.config p j I A 0)
      (inputs p m F j J n U0 a b scale I Q)=WeightedGlobalArenaSeedCandidate.config p (j+1) I A 0 := by sorry
