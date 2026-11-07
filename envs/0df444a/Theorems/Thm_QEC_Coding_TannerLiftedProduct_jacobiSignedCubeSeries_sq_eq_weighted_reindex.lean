-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiSignedCubeSeries_sq_eq_weighted_reindex
-- name    : QEC.Coding.TannerLiftedProduct.jacobiSignedCubeSeries_sq_eq_weighted_reindex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:17:08.933228+00:00
-- url     : https://prove2.me/theorems/5fb313eb-ceef-48ba-8c3e-055971ff86f4
-- title:
--   Tanner Lifted Product: jacobi Signed Cube Series sq eq weighted reindex
-- statement:
--   Coefficientwise form of Jacobi's parity reindexing: the square of the
--   signed cube series is the difference of the two weighted theta products.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L462-L483
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L462-L483

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.jacobiSignedCubeSeries_sq_eq_weighted_reindex :
    jacobiSignedCubeSeries ^ 2 =
      PowerSeries.C (1 / 2 : ℚ) *
        (rationalIntegerThetaSeries * jacobiWeightedTriangularSeries -
          jacobiWeightedSquareSeries * rationalBilateralTriangularSeries) := by sorry
