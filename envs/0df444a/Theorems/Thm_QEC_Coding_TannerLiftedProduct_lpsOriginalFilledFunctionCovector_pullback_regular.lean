-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledFunctionCovector_pullback_regular
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledFunctionCovector_pullback_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:05:31.435026+00:00
-- url     : https://prove2.me/theorems/d01e0e4c-eba0-4a63-bd2d-418690d71d33
-- title:
--   Tanner Lifted Product: lps Original Filled Function Covector pullback regular
-- statement:
--   Actual original differential compatibility used by the comparison or its semantic fixture.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicDifferentialComparison.lean#L872-L904
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicDifferentialComparison.lean#L872-L904

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane Manifold
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
local notation "R" => LPSOriginalFilledMeromorphicFunctionRing N hN
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local notation "V" => LPSOriginalFilledMeromorphicCovectorRepresentatives N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_391f8f7aa3_629
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_391f8f7aa3_630
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledFunctionCovector_pullback_regular
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ) (z : ℂ) (hz : 0 < z.im)
    (hF : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F
        (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z))) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    lpsOriginalFilledFunctionCovector N hN F
      (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z))
      (mfderiv 𝓘(ℂ) 𝓘(ℂ)
        (fun w : ℂ => lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex w))
          z (1 : ℂ)) = deriv (lpsOriginalFilledMeromorphicPullback N F) z := by sorry
