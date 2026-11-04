-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrimitiveBounds_word_bound
-- name    : ThreeSum.WeightedGlobalArenaPrimitiveBounds.word_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:33:35.725593+00:00
-- url     : https://prove2.me/theorems/10c8e4b0-3922-457d-aa8e-ffcc507c438e
-- title:
--   Weighted Global Arena Primitive Bounds: word bound
-- statement:
--   The Weighted Global Arena Primitive Bounds construction uses the word bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrimitiveBounds.lean#L24-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrimitiveBounds.lean#L24-L46

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedPrimitiveGuards
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrimitiveBounds
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrimitiveBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaPrimitiveBounds.word_bound (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (A : Inputs) (seed positionCap n U : ℕ)
    (D : Data (config p r I A seed))
    (hJ : A.J=LightWeightedGlobalDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n) (hpos : positionCap≤n)
    (hB : D.bB<p) (hC : D.bC<p) (hO : D.bO<p) :
    WeightedGlobalArenaSeedPrimitiveGuards.word maps τ I A seed positionCap D≤
      (numbers maps τ cap M b K H drift scale n U r).sourceWord := by sorry
