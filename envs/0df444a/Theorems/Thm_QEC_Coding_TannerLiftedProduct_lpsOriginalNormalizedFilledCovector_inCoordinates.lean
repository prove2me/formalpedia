-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledCovector_inCoordinates
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledCovector_inCoordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:30:52.421202+00:00
-- url     : https://prove2.me/theorems/62b651b8-bd1d-4ed2-975b-53bcb6e525cf
-- title:
--   Tanner Lifted Product: lps Original Normalized Filled Covector in Coordinates
-- statement:
--   The whole repaired covector in any chart is multiplication by its normalized coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeCovectorNormalForm.lean#L65-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeCovectorNormalForm.lean#L65-L117

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorCoordinates
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorNormalForm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledCovector_inCoordinates
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN)
    (hmer : lpsOriginalFilledCovectorChartMeromorphic N hN sigma)
    (x y : LPSOriginalFilledCurve N)
    (hy : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      y ∈ (chartAt ℂ x).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ)) ℂ
      (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x y x y
      (lpsOriginalNormalizedFilledCovector N hN sigma y) =
      ContinuousLinearMap.mul ℂ ℂ
        (toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma x)
          (chartAt ℂ x y) (chartAt ℂ x y)) := by sorry
