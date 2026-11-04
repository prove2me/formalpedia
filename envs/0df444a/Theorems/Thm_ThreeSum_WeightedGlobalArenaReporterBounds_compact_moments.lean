-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaReporterBounds_compact_moments
-- name    : ThreeSum.WeightedGlobalArenaReporterBounds.compact_moments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:14:16.926315+00:00
-- url     : https://prove2.me/theorems/76096b30-5799-4655-8842-a02f4b34f7cd
-- title:
--   Weighted Global Arena Reporter Bounds: compact moments
-- statement:
--   The Weighted Global Arena Reporter Bounds construction uses the compact moments property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaReporterBounds.lean#L25-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaReporterBounds.lean#L25-L39

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

theorem ThreeSum.WeightedGlobalArenaReporterBounds.compact_moments {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
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
