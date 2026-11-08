-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCovectorChartCoefficient_cocycle
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCovectorChartCoefficient_cocycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:25:27.115103+00:00
-- url     : https://prove2.me/theorems/f93ee8c9-e265-41d3-afbe-5647cc173f82
-- title:
--   Tanner Lifted Product: lps Original Filled Covector Chart Coefficient cocycle
-- statement:
--   Any actual cotangent representative obeys the derivative-weighted chart cocycle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeCovectorCoordinates.lean#L20-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeCovectorCoordinates.lean#L20-L63

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeLocalDifferentialComparison
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_NormalizedGermUnits
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorCoordinates
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCovectorChartCoefficient_cocycle
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN)
    (x y : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z ∈ ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    let g := (chartAt ℂ x).symm.trans (chartAt ℂ y)
    lpsOriginalFilledCovectorChartCoefficient N hN sigma x z =
      lpsOriginalFilledCovectorChartCoefficient N hN sigma y (g z) * deriv g z := by sorry
