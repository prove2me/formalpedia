-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledCovector_chart
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledCovector_chart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:29:50.641805+00:00
-- url     : https://prove2.me/theorems/a829d97e-eb45-4010-b1a9-9d26afd6a58c
-- title:
--   Tanner Lifted Product: lps Original Normalized Filled Covector chart
-- statement:
--   The genuine repaired chart coefficient equals the chartwise meromorphic normal form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeCovectorNormalForm.lean#L120-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeCovectorNormalForm.lean#L120-L142

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorCoordinates
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorNormalForm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledCovector_chart
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN)
    (hmer : lpsOriginalFilledCovectorChartMeromorphic N hN sigma)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z ∈ (chartAt ℂ x).target) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    lpsOriginalFilledCovectorChartCoefficient N hN (lpsOriginalNormalizedFilledCovector N hN sigma)
      x z = toMeromorphicNFOn (lpsOriginalFilledCovectorChartCoefficient N hN sigma x)
        (chartAt ℂ x).target z := by sorry
