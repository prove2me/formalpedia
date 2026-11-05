-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaReporterBounds_compact_scores
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds.compact_scores
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:52:37.025306+00:00
-- url     : https://prove2.me/theorems/997e2b47-d119-40e4-8ad0-45de650e91b5
-- title:
--   compact_scores
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaReporterBounds.lean#L41-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaReporterBounds.lean#L41-L57

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds.compact_scores {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
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
