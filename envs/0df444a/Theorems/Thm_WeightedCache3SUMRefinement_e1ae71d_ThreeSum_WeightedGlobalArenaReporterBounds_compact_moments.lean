-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaReporterBounds_compact_moments
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds.compact_moments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:52:57.193626+00:00
-- url     : https://prove2.me/theorems/22d11338-7b7a-40a3-ad66-b384b2ba6568
-- title:
--   compact_moments
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaReporterBounds.lean#L25-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaReporterBounds.lean#L25-L39

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds.compact_moments {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (keysB keysC : ℕ→ℕ) (B C : ℕ→ℤ) (nB nC pairMass U H : ℕ)
    (hleftCount : S.left.NL=(indices keysB nB).length)
    (hrightCount : S.right.NL=(indices keysC nC).length)
    (hpairs : pairBound S*2^N≤pairMass)
    (hB : ∀ i<nB, |B i|≤(U : ℤ)) (hC : ∀ i<nC, |C i|≤(U : ℤ)) :
    ∀ i, ∀ k≤2*H,
      |∑ p : WeightedGlobalNativePairMoments.Pair S i,
        WeightedGlobalNativePairMoments.mass S i p*WeightedGlobalNativePairMoments.mode
          (LightWeightedGlobalPostSelection.compact keysB B nB)
          (LightWeightedGlobalPostSelection.compact keysC C nC) p^k|
        ≤(WeightedGlobalMomentDetectorResources.input pairMass U H : ℤ) := by sorry
