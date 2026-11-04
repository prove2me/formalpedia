-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaTensorBounds_spatial
-- name    : ThreeSum.WeightedGlobalArenaTensorBounds.spatial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:55:19.952973+00:00
-- url     : https://prove2.me/theorems/ccc77b2f-4007-40da-a6d2-665781dd1a63
-- title:
--   Weighted Global Arena Tensor Bounds: spatial
-- statement:
--   The Weighted Global Arena Tensor Bounds construction uses the spatial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorBounds.lean#L89-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorBounds.lean#L89-L102

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorBounds
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaTensorBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaFrontBounds WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
open WeightedGlobalNativeCompleteFrontend WeightedGlobalNativeMomentBounds
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaTensorBounds.spatial (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (n U : ℕ)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (HC : Fits I.capacity (numbers maps τ cap M b K H drift scale n U r)) :
    106≤I.capacity ∧ 4≤I.capacity ∧ 5≤I.capacity ∧
    TernaryPairedColumnEnumeration.width K+1≤I.capacity ∧
    (entries (r := r) maps τ I).length*(LightWeightedGlobalDimensions.J M b n U+2)^4≤I.capacity := by sorry
