-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiEulerSixProduct_eq_tprod_pow
-- name    : QEC.Coding.TannerLiftedProduct.jacobiEulerSixProduct_eq_tprod_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:56:24.754632+00:00
-- url     : https://prove2.me/theorems/32c1b098-223f-474d-afff-eced6c1a23b8
-- title:
--   Tanner Lifted Product: jacobi Euler Six Product eq tprod pow
-- statement:
--   Euler's sixth-power product is the sixth power of Euler's product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L260-L265
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L260-L265

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.jacobiEulerSixProduct_eq_tprod_pow :
    jacobiEulerSixProduct =
      (∏' n : ℕ,
        ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1))) ^ 6 := by sorry
