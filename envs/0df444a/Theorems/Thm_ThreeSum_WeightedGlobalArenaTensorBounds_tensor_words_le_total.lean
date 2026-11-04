-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaTensorBounds_tensor_words_le_total
-- name    : ThreeSum.WeightedGlobalArenaTensorBounds.tensor_words_le_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:09:47.112708+00:00
-- url     : https://prove2.me/theorems/f2b99463-1bac-4174-a652-b036f4835145
-- title:
--   Weighted Global Arena Tensor Bounds: tensor words le total
-- statement:
--   The Weighted Global Arena Tensor Bounds construction uses the tensor words le total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorBounds.lean#L79-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorBounds.lean#L79-L87

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

theorem ThreeSum.WeightedGlobalArenaTensorBounds.tensor_words_le_total (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U j : ℕ) :
    (numbers maps τ cap M b K H drift scale n U j).potentialWord+
      (numbers maps τ cap M b K H drift scale n U j).tensorWord≤
      total maps τ cap M b K H drift scale n U j := by sorry
