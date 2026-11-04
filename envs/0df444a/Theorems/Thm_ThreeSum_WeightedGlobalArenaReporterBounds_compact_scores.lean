-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaReporterBounds_compact_scores
-- name    : ThreeSum.WeightedGlobalArenaReporterBounds.compact_scores
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:14:09.587011+00:00
-- url     : https://prove2.me/theorems/9eaca663-1537-4d90-98ad-e9160a819284
-- title:
--   Weighted Global Arena Reporter Bounds: compact scores
-- statement:
--   The Weighted Global Arena Reporter Bounds construction uses the compact scores property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaReporterBounds.lean#L41-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaReporterBounds.lean#L41-L57

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

theorem ThreeSum.WeightedGlobalArenaReporterBounds.compact_scores {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (keysB keysC : ℕ→ℕ) (B C : ℕ→ℤ) (nB nC pairMass U K : ℕ)
    (hleftCount : S.left.NL=(indices keysB nB).length)
    (hrightCount : S.right.NL=(indices keysC nC).length)
    (hpairs : pairBound S*2^N≤pairMass)
    (hB : ∀ i<nB, |B i|≤(U : ℤ)) (hC : ∀ i<nC, |C i|≤(U : ℤ)) :
    ∀ k<K+1, ∀ j≤k, ∀ i,
      |LightWeightedGlobalMomentChannelFactory.score S
        (LightWeightedGlobalPostSelection.compact keysB B nB)
        (LightWeightedGlobalPostSelection.compact keysC C nC) k j i|
        ≤(WeightedGlobalMomentChannelResources.scoreBound pairMass U K : ℤ) := by sorry
