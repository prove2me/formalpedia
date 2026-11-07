-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiAlternatingThetaProduct_eq_even_mul_oddSquare
-- name    : QEC.Coding.TannerLiftedProduct.jacobiAlternatingThetaProduct_eq_even_mul_oddSquare
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:51:38.643168+00:00
-- url     : https://prove2.me/theorems/46191129-7b3a-40b2-ac1f-8d486af948dd
-- title:
--   Tanner Lifted Product: jacobi Alternating Theta Product eq even mul odd Square
-- statement:
--   The Tanner Lifted Product construction uses the jacobi Alternating Theta Product eq even mul odd Square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L348-L354
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L348-L354

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

theorem QEC.Coding.TannerLiftedProduct.jacobiAlternatingThetaProduct_eq_even_mul_oddSquare :
    jacobiAlternatingThetaProduct =
      jacobiEvenMinusProduct * jacobiOddMinusSquareProduct := by sorry
