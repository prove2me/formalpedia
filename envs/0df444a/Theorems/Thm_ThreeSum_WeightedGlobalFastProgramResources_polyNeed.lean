-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFastProgramResources_polyNeed
-- name    : ThreeSum.WeightedGlobalFastProgramResources.polyNeed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:59:28.486782+00:00
-- url     : https://prove2.me/theorems/8e0d181c-2440-4e46-97e2-33eed07f1383
-- title:
--   Weighted Global Fast Program Resources: poly Need
-- statement:
--   The Weighted Global Fast Program Resources construction uses the poly Need property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramResources.lean#L57-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramResources.lean#L57-L79

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_Submission_ThreeSum_ThreeSumColorDriverResources
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFastProgramResources
open Light LightWeightedGlobalFastProgram LightWeightedGlobalFastProgramProof
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalFastProgramResources.polyNeed {M b p K : ℕ} [Fact p.Prime] (hM : 1<M) (hb : 1<b) (κ : ℕ)
    {colorNeed : ℕ→ℕ→Need} (hc : PolyNeed colorNeed) :
    PolyNeed (need M b p K κ colorNeed) := by sorry
