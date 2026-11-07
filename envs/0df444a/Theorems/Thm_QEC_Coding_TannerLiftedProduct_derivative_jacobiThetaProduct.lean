-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_derivative_jacobiThetaProduct
-- name    : QEC.Coding.TannerLiftedProduct.derivative_jacobiThetaProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:25:34.398553+00:00
-- url     : https://prove2.me/theorems/f736c314-5790-4bcc-a5fe-027f9418db8f
-- title:
--   Tanner Lifted Product: derivative jacobi Theta Product
-- statement:
--   Infinite-product differentiation for the Jacobi theta product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L228-L235
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L228-L235

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.derivative_jacobiThetaProduct :
    PowerSeries.derivative ℚ jacobiThetaProduct =
      jacobiThetaProduct * jacobiThetaLogDerivative := by sorry
