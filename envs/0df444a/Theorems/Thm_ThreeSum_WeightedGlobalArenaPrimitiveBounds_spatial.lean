-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrimitiveBounds_spatial
-- name    : ThreeSum.WeightedGlobalArenaPrimitiveBounds.spatial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:31:12.550128+00:00
-- url     : https://prove2.me/theorems/31ffbb4a-83e2-4ef8-9a42-2cce1e92f7d8
-- title:
--   Weighted Global Arena Primitive Bounds: spatial
-- statement:
--   The Weighted Global Arena Primitive Bounds construction uses the spatial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrimitiveBounds.lean#L49-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrimitiveBounds.lean#L49-L89

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedPrimitiveGuards
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrimitiveBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrimitiveBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaPrimitiveBounds.spatial (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (A : Inputs) (n U : ℕ)
    (hJ : A.J=LightWeightedGlobalDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (HC : Fits I.capacity (numbers maps τ cap M b K H drift scale n U r)) :
    I.nB≤I.capacity ∧ I.nC≤I.capacity ∧ I.requesterCount≤I.capacity ∧
    A.J+2≤I.capacity ∧ A.J*p^(r-1)≤I.capacity ∧ p^(r-1)*p≤I.capacity ∧
    3*I.requesterCount*(F*WeightedGlobalGoodOutputCatalog.cap m p τ)^r≤I.capacity ∧
    Nat.log 2 (2*WeightedGlobalArenaSeedPrimitiveGuards.rawCap m p r+1)+2≤I.capacity := by sorry
