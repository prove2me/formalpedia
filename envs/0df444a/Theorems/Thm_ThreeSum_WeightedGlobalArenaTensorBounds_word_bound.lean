-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaTensorBounds_word_bound
-- name    : ThreeSum.WeightedGlobalArenaTensorBounds.word_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:09:19.776198+00:00
-- url     : https://prove2.me/theorems/406aedcf-4e82-48c0-ae02-0d9a8fc6331c
-- title:
--   Weighted Global Arena Tensor Bounds: word bound
-- statement:
--   The Weighted Global Arena Tensor Bounds construction uses the word bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorBounds.lean#L56-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorBounds.lean#L56-L76

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaTensorBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaFrontBounds WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
open WeightedGlobalNativeCompleteFrontend WeightedGlobalNativeMomentBounds
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaTensorBounds.word_bound (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (n U tagBound : ℕ)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (hweight : I.weightCap≤weight H (4^fixedLength m) U)
    (htag : tagBound≤2*(4^fixedLength m)+1) :
    WeightedGlobalTensorWordResources.word K (LightWeightedGlobalDimensions.J M b n U)
      (entries (r := r) maps τ I).length (scoreBound (setup (r := r) maps τ cap Q I)) tagBound≤
      (numbers maps τ cap M b K H drift scale n U r).potentialWord+
        (numbers maps τ cap M b K H drift scale n U r).tensorWord := by sorry
