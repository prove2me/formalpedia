-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaReporterBounds_channel_words
-- name    : ThreeSum.WeightedGlobalArenaReporterBounds.channel_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:13:52.358376+00:00
-- url     : https://prove2.me/theorems/6fc20d83-5b25-4186-8aa4-3b893780f679
-- title:
--   Weighted Global Arena Reporter Bounds: channel words
-- statement:
--   The Weighted Global Arena Reporter Bounds construction uses the channel words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaReporterBounds.lean#L59-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaReporterBounds.lean#L59-L80

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_Weighted_Global_TernaryArenaReporterBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaReporterBounds
open Light WeightedGlobalArenaLayout LightOriginalSurvivors
open WeightedGlobalNativeMomentBounds WeightedGlobalMomentWeightBounds

theorem ThreeSum.WeightedGlobalArenaReporterBounds.channel_words (lim : Limits) (pairMass U K : ℕ)
    (hw : ((WeightedGlobalMomentChannelResources.need pairMass U K).word : ℤ)≤lim.word) :
    (∀ k<K+1, ∀ j≤k,
      max (U : ℤ) (2*((k.choose j : ℤ)+1)*((U : ℤ)+2)^j)≤lim.word) ∧
    (∀ k<K+1, ∀ j≤k,
      max (U : ℤ) (2*((U : ℤ)+1)^(k-j))≤lim.word) ∧
    2*(((TernaryMomentSchedule.channels (K+1)).length*
      WeightedGlobalMomentChannelResources.scoreBound pairMass U K : ℕ) : ℤ)≤lim.word ∧
    (K+1 : ℕ)≤lim.word := by sorry
