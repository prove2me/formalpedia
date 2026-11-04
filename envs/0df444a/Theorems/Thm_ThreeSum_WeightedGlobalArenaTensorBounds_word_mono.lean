-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaTensorBounds_word_mono
-- name    : ThreeSum.WeightedGlobalArenaTensorBounds.word_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:19:17.600478+00:00
-- url     : https://prove2.me/theorems/8997c971-6231-4c84-b59e-2b55d71bc33d
-- title:
--   Weighted Global Arena Tensor Bounds: word mono
-- statement:
--   The Weighted Global Arena Tensor Bounds construction uses the word mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorBounds.lean#L48-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorBounds.lean#L48-L54

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorBounds
import Theorems.Thm_ThreeSum_LightExtensionFactorPredicate_word_mono
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_word_mono
import Theorems.Thm_ThreeSum_LightExtensionQuotientSearch_word_mono
import Theorems.Thm_ThreeSum_LightRadixKeys_word_mono
import Theorems.Thm_ThreeSum_ModuloRuntime_word_mono
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_word_mono

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaTensorBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaFrontBounds WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
open WeightedGlobalNativeCompleteFrontend WeightedGlobalNativeMomentBounds
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaTensorBounds.word_mono {K J count count' V V' U U' : ℕ}
    (hc : count≤count') (hv : V≤V') (hu : U≤U') :
    WeightedGlobalTensorWordResources.word K J count V U≤
      WeightedGlobalTensorWordResources.word K J count' V' U' := by sorry
