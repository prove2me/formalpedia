-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPostSelection_support
-- name    : ThreeSum.WeightedGlobalArenaPostSelection.support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:28:26.631806+00:00
-- url     : https://prove2.me/theorems/2c56eea7-3d30-4e7a-ab4e-f07eb9577dc4
-- title:
--   Weighted Global Arena Post Selection: support
-- statement:
--   The Weighted Global Arena Post Selection construction uses the support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostSelection.lean#L64-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostSelection.lean#L64-L104

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCompactSupport
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_Submission_Weighted_Global_TernaryArenaMomentResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCountSeed
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostSelection
import Theorems.Thm_ThreeSum_TernaryTaggedMinorSupport_support
import Theorems.Thm_ThreeSum_WeightedGlobalArenaCompactSupport_support
import Theorems.Thm_ThreeSum_WeightedGlobalCompactPairedSupport_support

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPostSelection
open Light LightOriginalSurvivors LightWeightedGlobalPostSelection
open WeightedGlobalArenaSourceSetup WeightedGlobalCoverGoodMaps TernarySignedReduction
open TernaryExtensionEncoding WeightedGlobalArenaLayout
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F r J : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaPostSelection.support (maps : Fin F→Weight m p) (τ cap K U radix nA : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input)
    (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ)
    (hb : 1<radix) (hp : 2*radix<p)
    (hB : ∀j<I.nB, |B j|≤(U : ℤ)) (hC : ∀k<I.nC, |C k|≤(U : ℤ))
    (hcap : 4*U<radix^J)
    (hkB : ∀j<I.nB, keysB j=coefficientCode (WeightedGlobalNativeRequesterCoverage.sourceLeft H U radix (B j)))
    (hkC : ∀j<I.nC, keysC j=coefficientCode (WeightedGlobalNativeRequesterCoverage.sourceRight H U radix (C j)))
    (hzero : WeightedGlobalNativeTensorScore.pairedPotential
      (setup (r := r) maps τ cap Q (WeightedGlobalArenaNativeComplete.input I U radix nA H A B C)) K J
      (fun j i => TernarySignedLayout.feature (leftRaw U radix J (B j)) i)
      (fun j i => TernarySignedLayout.feature (rightRaw U radix J (C j)) i)=0) :
    let S := setup (r := r) maps τ cap Q (selectedInput I U radix nA H A B C keysB keysC)
    ∀i<S.front.count,
      (TernaryPairedSupport.physicalSupport
        (WeightedGlobalNativePairMoments.mode (compact keysB B I.nB) (compact keysC C I.nC)
          (S := S) (i := i))).card≤2*p^K := by sorry
