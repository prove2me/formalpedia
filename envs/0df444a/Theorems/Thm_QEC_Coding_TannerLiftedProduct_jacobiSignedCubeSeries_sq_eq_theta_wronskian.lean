-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiSignedCubeSeries_sq_eq_theta_wronskian
-- name    : QEC.Coding.TannerLiftedProduct.jacobiSignedCubeSeries_sq_eq_theta_wronskian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:32:23.883081+00:00
-- url     : https://prove2.me/theorems/a08827d9-1dc0-4354-bd9f-8452a113409e
-- title:
--   Tanner Lifted Product: jacobi Signed Cube Series sq eq theta wronskian
-- statement:
--   Series-side Jacobi cube identity after the parity reindexing.  The only
--   remaining cube input is the specialized triple-product identity identifying
--   `jacobiSignedCubeSeries` with Euler's cubed product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L498-L511
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L498-L511

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.jacobiSignedCubeSeries_sq_eq_theta_wronskian :
    jacobiSignedCubeSeries ^ 2 =
      rationalIntegerThetaSeries * rationalTriangularThetaSeries +
        PowerSeries.C 4 * PowerSeries.X *
          (rationalIntegerThetaSeries *
              PowerSeries.derivative ℚ rationalTriangularThetaSeries -
            PowerSeries.derivative ℚ rationalIntegerThetaSeries *
              rationalTriangularThetaSeries) := by sorry
