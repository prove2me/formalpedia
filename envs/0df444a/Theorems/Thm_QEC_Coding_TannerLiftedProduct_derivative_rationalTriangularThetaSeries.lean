-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_derivative_rationalTriangularThetaSeries
-- name    : QEC.Coding.TannerLiftedProduct.derivative_rationalTriangularThetaSeries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:17:12.030203+00:00
-- url     : https://prove2.me/theorems/5b21faad-23b0-418d-af49-de0f4039f329
-- title:
--   Tanner Lifted Product: derivative rational Triangular Theta Series
-- statement:
--   Differentiating the normalized triangular series only differentiates
--   its bilateral nonconstant factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L487-L493
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L487-L493

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.derivative_rationalTriangularThetaSeries :
    PowerSeries.derivative ℚ rationalTriangularThetaSeries =
      PowerSeries.C (1 / 2 : ℚ) *
        PowerSeries.derivative ℚ rationalBilateralTriangularSeries := by sorry
