-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedCovectorCoefficient_cocycle
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedCovectorCoefficient_cocycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:28:52.107646+00:00
-- url     : https://prove2.me/theorems/6e417b4b-31da-494f-a9ee-992c1bed33a1
-- title:
--   Tanner Lifted Product: lps Original Normalized Covector Coefficient cocycle
-- statement:
--   Actual normalized coefficient values obey the derivative-weighted chart cocycle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeCovectorNormalForm.lean#L19-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeCovectorNormalForm.lean#L19-L51

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorCoordinates
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorNormalForm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedCovectorCoefficient_cocycle
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN)
    (hmer : lpsOriginalFilledCovectorChartMeromorphic N hN sigma)
    (x y : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z ∈ ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    let g := (chartAt ℂ x).symm.trans (chartAt ℂ y)
    toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma x) z z =
      toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma y)
        (g z) (g z) * deriv g z := by sorry
