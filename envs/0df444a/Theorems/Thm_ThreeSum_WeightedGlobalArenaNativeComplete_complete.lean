-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaNativeComplete_complete
-- name    : ThreeSum.WeightedGlobalArenaNativeComplete.complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:50:32.951634+00:00
-- url     : https://prove2.me/theorems/6347075e-fc08-4569-ab20-07191f5491ba
-- title:
--   Weighted Global Arena Native Complete: complete
-- statement:
--   Unconditional finite correctness of the actual canonical native
--   representation, for every admissible original colored input and every row map.
--   Only the local family's genuine cover property and digit capacity are used.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaNativeComplete.lean#L34-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaNativeComplete.lean#L34-L56

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
import Theorems.Thm_ThreeSum_TernaryNearCanonical_complete
import Theorems.Thm_ThreeSum_WeightedGlobalCanonicalNativeCompleteness_complete
import Theorems.Thm_ThreeSum_WeightedGlobalNativeCompleteFrontend_complete
import Theorems.Thm_ThreeSum_WeightedGlobalNativeRequesterCoverage_complete
import Theorems.Thm_ThreeSum_WeightedNearCanonical_complete

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaNativeComplete
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernarySignedReduction
open WeightedGlobalArenaSourceSetup TernaryExtensionEncoding WeightedGlobalNativeRequesterCoverage
variable {p m F r J : ℕ} [Fact p.Prime]
set_option maxHeartbeats 4000000

theorem ThreeSum.WeightedGlobalArenaNativeComplete.complete (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (U radix nA : ℕ)
    (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p)) (A B C : ℕ→ℤ)
    (hcover : ∀a b : ZMod p, ∃i, WeightedGlobalCoverFrequency.Covers m p cap τ (maps i) (a,b))
    (hA : ∀i<nA, |A i|≤(U : ℤ)) (hB : ∀j<I.nB, |B j|≤(U : ℤ))
    (hC : ∀k<I.nC, |C k|≤(U : ℤ)) (hcap : 4*U<radix^J) :
    let I' := input I U radix nA H A B C
    let S := setup (r := r) maps τ cap Q I'
    (∃i<S.front.count, ∃pair : WeightedGlobalNativePairMoments.Pair S i,
      WeightedGlobalNativePairMoments.mode B C pair=A (originalPosition (r := r) maps τ I' i)) ↔
      ∃i<nA, ∃j<I.nB, ∃k<I.nC, C k=A i+B j := by sorry
