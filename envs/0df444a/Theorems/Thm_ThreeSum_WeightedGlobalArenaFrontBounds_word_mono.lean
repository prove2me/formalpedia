-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_word_mono
-- name    : ThreeSum.WeightedGlobalArenaFrontBounds.word_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:05:30.855003+00:00
-- url     : https://prove2.me/theorems/af2671c4-82cb-4c97-bcaa-ac419ee84dd6
-- title:
--   Weighted Global Arena Front Bounds: word mono
-- statement:
--   The Weighted Global Arena Front Bounds construction uses the word mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFrontBounds.lean#L32-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFrontBounds.lean#L32-L38

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCountReady
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontBounds
import Theorems.Thm_ThreeSum_LightExtensionFactorPredicate_word_mono
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_word_mono
import Theorems.Thm_ThreeSum_LightExtensionQuotientSearch_word_mono
import Theorems.Thm_ThreeSum_LightRadixKeys_word_mono
import Theorems.Thm_ThreeSum_ModuloRuntime_word_mono

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFrontBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaFrontBounds.word_mono {N nb nb' G count count' R R' V V' : ℕ}
    (hb : nb≤nb') (hc : count≤count') (hr : R≤R') (hv : V≤V') :
    WeightedGlobalFrontendResources.word N nb G count R V≤
      WeightedGlobalFrontendResources.word N nb' G count' R' V' := by sorry
