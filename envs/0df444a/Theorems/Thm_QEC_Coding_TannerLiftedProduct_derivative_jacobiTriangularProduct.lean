-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_derivative_jacobiTriangularProduct
-- name    : QEC.Coding.TannerLiftedProduct.derivative_jacobiTriangularProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:25:56.728117+00:00
-- url     : https://prove2.me/theorems/f42dd5bf-fbc6-486d-8265-4ee6c9800152
-- title:
--   Tanner Lifted Product: derivative jacobi Triangular Product
-- statement:
--   Infinite-product differentiation for the Jacobi triangular product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L271-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L271-L278

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.derivative_jacobiTriangularProduct :
    PowerSeries.derivative ℚ jacobiTriangularProduct =
      jacobiTriangularProduct * jacobiTriangularLogDerivative := by sorry
