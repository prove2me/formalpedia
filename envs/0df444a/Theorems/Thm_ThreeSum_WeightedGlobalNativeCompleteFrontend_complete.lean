-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeCompleteFrontend_complete
-- name    : ThreeSum.WeightedGlobalNativeCompleteFrontend.complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:12:23.094824+00:00
-- url     : https://prove2.me/theorems/d609583c-1d23-4d07-afb8-f899a90fdeda
-- title:
--   Weighted Global Native Complete Frontend: complete
-- statement:
--   The Weighted Global Native Complete Frontend construction uses the complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeCompleteFrontend.lean#L67-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeCompleteFrontend.lean#L67-L129

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeRequesterCoverage
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
import Definitions.Def_Submission_Weighted_Global_TernaryNativeCompleteFrontend
import Theorems.Thm_ThreeSum_TernaryNearCanonical_complete
import Theorems.Thm_ThreeSum_WeightedGlobalCanonicalNativeCompleteness_complete
import Theorems.Thm_ThreeSum_WeightedGlobalNativeRequesterCoverage_complete
import Theorems.Thm_ThreeSum_WeightedNearCanonical_complete

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeCompleteFrontend
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCanonicalDictionaries
open TernaryExtensionEncoding WeightedGlobalNativeRequesterCoverage
open WeightedGlobalCanonicalNativeCompleteness LightTernarySourceHost
set_option maxHeartbeats 4000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalNativeCompleteFrontend.complete {J U radix nA : ℕ}
    (S : WeightedSourceCountExecutionFactory.Setup (r*fixedLength m))
    (maps : Fin F→Weight m p) (cap τ : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ i, WeightedGlobalCoverFrequency.Covers m p cap τ (maps i) (a,b))
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (pos : ℕ→ℕ)
    (hsources : Sources S maps cap) (hqueries : Queries S maps τ U radix H A nA pos)
    (hleft : ∀j<S.left.NL, S.left.input j=(coefficientCode (sourceLeft H U radix (B j)) : ℤ))
    (hright : ∀j<S.right.NL, S.right.input j=(coefficientCode (sourceRight H U radix (C j)) : ℤ))
    (hA : ∀i<nA, |A i|≤(U : ℤ)) (hB : ∀j<S.left.NL, |B j|≤(U : ℤ))
    (hC : ∀k<S.right.NL, |C k|≤(U : ℤ)) (hcap : 4*U<radix^J) :
    (∃ i<S.front.count, ∃ pair : WeightedGlobalNativePairMoments.Pair S i,
      WeightedGlobalNativePairMoments.mode B C pair=A (pos i)) ↔
      (∃ i<nA, ∃j<S.left.NL, ∃k<S.right.NL, C k=A i+B j) := by sorry
