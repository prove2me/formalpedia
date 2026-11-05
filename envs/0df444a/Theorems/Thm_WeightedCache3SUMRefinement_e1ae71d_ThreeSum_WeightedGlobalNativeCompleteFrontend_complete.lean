-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeCompleteFrontend_complete
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeCompleteFrontend.complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:57:09.022291+00:00
-- url     : https://prove2.me/theorems/419673bd-d556-4d9a-aa1d-77bb4a66d429
-- title:
--   complete
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeCompleteFrontend.lean#L67-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeCompleteFrontend.lean#L67-L129

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeRequesterCoverage
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeCompleteFrontend
import Theorems.Thm_ThreeSum_TernaryNearCanonical_complete
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCanonicalNativeCompleteness_complete
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeRequesterCoverage_complete
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearCanonical_complete

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeCompleteFrontend
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCanonicalDictionaries
open TernaryExtensionEncoding WeightedGlobalNativeRequesterCoverage
open WeightedGlobalCanonicalNativeCompleteness LightTernarySourceHost
set_option maxHeartbeats 4000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeCompleteFrontend.complete {J U radix nA : ℕ}
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
