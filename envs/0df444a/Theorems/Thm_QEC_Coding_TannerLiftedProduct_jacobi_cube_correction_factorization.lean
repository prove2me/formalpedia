-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobi_cube_correction_factorization
-- name    : QEC.Coding.TannerLiftedProduct.jacobi_cube_correction_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:52:07.487194+00:00
-- url     : https://prove2.me/theorems/f1e1cdb9-f8f4-4782-9536-19c557a427f0
-- title:
--   Tanner Lifted Product: jacobi cube correction factorization
-- statement:
--   The right-hand side of Jacobi's cube/reindex identity is already a
--   product of `βγ` and one explicit logarithmic-derivative correction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L300-L311
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L300-L311

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.jacobi_cube_correction_factorization :
    jacobiThetaProduct * jacobiTriangularProduct +
        PowerSeries.C 4 * PowerSeries.X *
          (jacobiThetaProduct *
              PowerSeries.derivative ℚ jacobiTriangularProduct -
            PowerSeries.derivative ℚ jacobiThetaProduct *
              jacobiTriangularProduct) =
      (jacobiThetaProduct * jacobiTriangularProduct) *
        (1 + PowerSeries.C 4 * PowerSeries.X *
          jacobiLogDerivativeDifference) := by sorry
