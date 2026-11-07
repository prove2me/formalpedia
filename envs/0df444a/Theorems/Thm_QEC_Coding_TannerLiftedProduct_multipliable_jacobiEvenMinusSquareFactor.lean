-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobiEvenMinusSquareFactor
-- name    : QEC.Coding.TannerLiftedProduct.multipliable_jacobiEvenMinusSquareFactor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:51:41.434202+00:00
-- url     : https://prove2.me/theorems/c3ab6e4e-0fb4-4f69-8a35-7d92b2676c3b
-- title:
--   Tanner Lifted Product: multipliable jacobi Even Minus Square Factor
-- statement:
--   The Tanner Lifted Product construction uses the multipliable jacobi Even Minus Square Factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L390-L393
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L390-L393

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

theorem QEC.Coding.TannerLiftedProduct.multipliable_jacobiEvenMinusSquareFactor :
    Multipliable (fun n : ℕ =>
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) ^ 2) := by sorry
