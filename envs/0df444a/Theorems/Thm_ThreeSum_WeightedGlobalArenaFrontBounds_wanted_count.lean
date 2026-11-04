-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_wanted_count
-- name    : ThreeSum.WeightedGlobalArenaFrontBounds.wanted_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:02:41.222603+00:00
-- url     : https://prove2.me/theorems/b7dfe49f-80cb-4473-90bb-4f46fded0df4
-- title:
--   Weighted Global Arena Front Bounds: wanted count
-- statement:
--   The Weighted Global Arena Front Bounds construction uses the wanted count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFrontBounds.lean#L19-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFrontBounds.lean#L19-L30

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCountReady
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFrontBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaFrontBounds.wanted_count (maps : Fin F→Weight m p) (τ : ℕ) (I : Input)
    (M b n U : ℕ) (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U)) :
    (entries (r := r) maps τ I).length≤
      n*2^(LightWeightedGlobalDimensions.J M b n U)*(wantedWidth maps τ)^r := by sorry
