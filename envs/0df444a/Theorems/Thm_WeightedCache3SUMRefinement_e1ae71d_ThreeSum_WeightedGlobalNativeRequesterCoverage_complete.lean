-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeRequesterCoverage_complete
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeRequesterCoverage.complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:41:28.117788+00:00
-- url     : https://prove2.me/theorems/576e09e3-aba8-4ed7-b7df-f25fabefc41a
-- title:
--   complete
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeRequesterCoverage.lean#L32-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeRequesterCoverage.lean#L32-L60

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairAccess
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeRequesterCoverage
import Theorems.Thm_ThreeSum_TernaryNearCanonical_complete
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCanonicalNativeCompleteness_complete
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearCanonical_complete

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeRequesterCoverage
open TernarySignedReduction TernarySignedDigits TernaryExtensionEncoding
set_option maxHeartbeats 2500000
variable {p : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeRequesterCoverage.complete {J r U radix n i : ℕ}
    (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p)) (A : ℕ→ℤ) (b c : ℤ)
    (hi : i<n) (ha : |A i|≤(U : ℤ)) (hb : |b|≤(U : ℤ)) (hc : |c|≤(U : ℤ))
    (hcap : 4*U<radix^J) (hrel : c=A i+b) :
    ∃ t<n*2^J, position J t=i ∧ target H U radix A t=
      (coefficientCode (sourceLeft H U radix b+sourceRight H U radix c) : ℤ) := by sorry
