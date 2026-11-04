-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_digits
-- name    : ThreeSum.WeightedGlobalArenaPrefixFootprints.digits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T20:57:47.908072+00:00
-- url     : https://prove2.me/theorems/d1369dff-883b-4a3b-a3db-40c39d43c140
-- title:
--   Weighted Global Arena Prefix Footprints: digits
-- statement:
--   The Weighted Global Arena Prefix Footprints construction uses the digits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixFootprints.lean#L71-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixFootprints.lean#L71-L75

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairMass
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsBudget
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCapacity
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
import Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixFootprints
open WeightedGlobalArenaLayout WeightedGlobalArenaPairMass WeightedGlobalSignedPadding
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
attribute [local semireducible] Uniform

theorem ThreeSum.WeightedGlobalArenaPrefixFootprints.digits {M b : ℕ} (hM : 1<M) (hb : 1<b) :
    Uniform M (fun n U _=>LightWeightedGlobalDimensions.J M b n U) := by sorry
