-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeRequesterCoverage_complete
-- name    : ThreeSum.WeightedGlobalNativeRequesterCoverage.complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:49:40.696225+00:00
-- url     : https://prove2.me/theorems/ad7a422a-9c3d-4710-a076-6904788db896
-- title:
--   Weighted Global Native Requester Coverage: complete
-- statement:
--   Every original requester and every genuine signed difference is present
--   in the actual finite carry-code enumeration, with its original position.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeRequesterCoverage.lean#L32-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeRequesterCoverage.lean#L32-L60

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairAccess
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix
import Definitions.Def_Submission_Weighted_Global_TernaryNativeRequesterCoverage
import Theorems.Thm_ThreeSum_TernaryNearCanonical_complete
import Theorems.Thm_ThreeSum_WeightedGlobalCanonicalNativeCompleteness_complete
import Theorems.Thm_ThreeSum_WeightedNearCanonical_complete

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeRequesterCoverage
open TernarySignedReduction TernarySignedDigits TernaryExtensionEncoding
set_option maxHeartbeats 2500000
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalNativeRequesterCoverage.complete {J r U radix n i : ℕ}
    (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p)) (A : ℕ→ℤ) (b c : ℤ)
    (hi : i<n) (ha : |A i|≤(U : ℤ)) (hb : |b|≤(U : ℤ)) (hc : |c|≤(U : ℤ))
    (hcap : 4*U<radix^J) (hrel : c=A i+b) :
    ∃ t<n*2^J, position J t=i ∧ target H U radix A t=
      (coefficientCode (sourceLeft H U radix b+sourceRight H U radix c) : ℤ) := by sorry
