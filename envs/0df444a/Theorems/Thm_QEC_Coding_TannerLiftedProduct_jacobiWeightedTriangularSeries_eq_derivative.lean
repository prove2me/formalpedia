-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiWeightedTriangularSeries_eq_derivative
-- name    : QEC.Coding.TannerLiftedProduct.jacobiWeightedTriangularSeries_eq_derivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:56:57.784661+00:00
-- url     : https://prove2.me/theorems/e0eaef4b-70f7-4450-b20b-00f9566182db
-- title:
--   Tanner Lifted Product: jacobi Weighted Triangular Series eq derivative
-- statement:
--   The triangular weight identity
--   `(2z+1)² = 1 + 4(z²+z)` becomes a derivative identity of series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean#L117-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean#L117-L138

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.jacobiWeightedTriangularSeries_eq_derivative :
    jacobiWeightedTriangularSeries =
      rationalBilateralTriangularSeries +
        PowerSeries.C 4 *
          (PowerSeries.X *
            PowerSeries.derivative ℚ rationalBilateralTriangularSeries) := by sorry
