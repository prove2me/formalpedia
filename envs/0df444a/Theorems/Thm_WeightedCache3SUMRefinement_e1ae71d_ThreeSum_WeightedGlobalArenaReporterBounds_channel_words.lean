-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaReporterBounds_channel_words
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds.channel_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:53:25.66383+00:00
-- url     : https://prove2.me/theorems/c8cbcc43-4f0d-4ea8-9dd4-6eca15924ff2
-- title:
--   channel_words
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaReporterBounds.lean#L59-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaReporterBounds.lean#L59-L80

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPostSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentChannelResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaReporterBounds
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds
open Light WeightedGlobalArenaLayout LightOriginalSurvivors
open WeightedGlobalNativeMomentBounds WeightedGlobalMomentWeightBounds

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds.channel_words (lim : Limits) (pairMass U K : ℕ)
    (hw : ((WeightedGlobalMomentChannelResources.need pairMass U K).word : ℤ)≤lim.word) :
    (∀ k<K+1, ∀ j≤k,
      max (U : ℤ) (2*((k.choose j : ℤ)+1)*((U : ℤ)+2)^j)≤lim.word) ∧
    (∀ k<K+1, ∀ j≤k,
      max (U : ℤ) (2*((U : ℤ)+1)^(k-j))≤lim.word) ∧
    2*(((TernaryMomentSchedule.channels (K+1)).length*
      WeightedGlobalMomentChannelResources.scoreBound pairMass U K : ℕ) : ℤ)≤lim.word ∧
    (K+1 : ℕ)≤lim.word := by sorry
