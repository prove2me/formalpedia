-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiThetaTriangular_wronskian
-- name    : QEC.Coding.TannerLiftedProduct.jacobiThetaTriangular_wronskian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:26:06.327185+00:00
-- url     : https://prove2.me/theorems/2c5ef215-1340-4036-ab1d-9de83c65a05a
-- title:
--   Tanner Lifted Product: jacobi Theta Triangular wronskian
-- statement:
--   The Wronskian `βγ' - β'γ` factors by `βγ`; this is the algebraic
--   bridge between the cube identity and the Lambert-series correction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L287-L296
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L287-L296

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.jacobiThetaTriangular_wronskian :
    jacobiThetaProduct *
        PowerSeries.derivative ℚ jacobiTriangularProduct -
      PowerSeries.derivative ℚ jacobiThetaProduct *
        jacobiTriangularProduct =
      (jacobiThetaProduct * jacobiTriangularProduct) *
        jacobiLogDerivativeDifference := by sorry
