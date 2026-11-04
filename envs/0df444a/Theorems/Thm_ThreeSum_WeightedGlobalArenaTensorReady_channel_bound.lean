-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaTensorReady_channel_bound
-- name    : ThreeSum.WeightedGlobalArenaTensorReady.channel_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:58:43.819573+00:00
-- url     : https://prove2.me/theorems/5884b749-d52d-491c-92c4-b57c0fa28c84
-- title:
--   Weighted Global Arena Tensor Ready: channel bound
-- statement:
--   The actual product channel uses two original tagged coordinates.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorReady.lean#L22-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorReady.lean#L22-L29

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCountSeed
import Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorReady
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaTensorReady
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalTensorFactory
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaTensorReady.channel_bound {J q n U : ℕ} (L : ℕ→ℕ→ℤ)
    (hL : ∀i<n,∀j<J+2, |L i j|≤(U : ℤ)) (i : ℕ) (hi : i<n) (a b : ℕ) :
    |L i (LightWeightedGlobalTensorDriver.digit J q a)*L i (LightWeightedGlobalTensorDriver.digit J q b)|≤(U^2 : ℕ) := by sorry
