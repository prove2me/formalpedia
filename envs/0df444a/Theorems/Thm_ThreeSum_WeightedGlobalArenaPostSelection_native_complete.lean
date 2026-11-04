-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPostSelection_native_complete
-- name    : ThreeSum.WeightedGlobalArenaPostSelection.native_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:35:47.080194+00:00
-- url     : https://prove2.me/theorems/2c456e38-2c90-4ced-b049-a7efb429b2ae
-- title:
--   Weighted Global Arena Post Selection: native complete
-- statement:
--   The Weighted Global Arena Post Selection construction uses the native complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostSelection.lean#L45-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostSelection.lean#L45-L62

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCompactSupport
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_Submission_Weighted_Global_TernaryArenaMomentResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCountSeed
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostSelection
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPostSelection
open Light LightOriginalSurvivors LightWeightedGlobalPostSelection
open WeightedGlobalArenaSourceSetup WeightedGlobalCoverGoodMaps TernarySignedReduction
open TernaryExtensionEncoding WeightedGlobalArenaLayout
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F r J : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaPostSelection.native_complete (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (U radix nA : ℕ)
    (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ)
    (hcover : ∀a b : ZMod p, ∃i, WeightedGlobalCoverFrequency.Covers m p cap τ (maps i) (a,b))
    (hA : ∀i<nA, |A i|≤(U : ℤ)) (hB : ∀j<I.nB, |B j|≤(U : ℤ))
    (hC : ∀k<I.nC, |C k|≤(U : ℤ)) (hcap : 4*U<radix^J) :
    let I' := selectedInput I U radix nA H A B C keysB keysC
    let S := setup (r := r) maps τ cap Q I'
    (∃i<S.front.count, ∃pair : WeightedGlobalNativePairMoments.Pair S i,
      WeightedGlobalNativePairMoments.mode (compact keysB B I.nB) (compact keysC C I.nC) pair=
        A (WeightedGlobalArenaNativeComplete.originalPosition (r := r) maps τ I' i)) ↔
      ∃i<nA, ∃j<(indices keysB I.nB).length, ∃k<(indices keysC I.nC).length,
        compact keysC C I.nC k=A i+compact keysB B I.nB j := by sorry
