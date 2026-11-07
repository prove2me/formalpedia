-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiEvenMinusSquareProduct_eq_evenMinusProduct_sq
-- name    : QEC.Coding.TannerLiftedProduct.jacobiEvenMinusSquareProduct_eq_evenMinusProduct_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:50:50.119005+00:00
-- url     : https://prove2.me/theorems/f24e96f5-2998-473d-b79e-f14870a4d476
-- title:
--   Tanner Lifted Product: jacobi Even Minus Square Product eq even Minus Product sq
-- statement:
--   The Tanner Lifted Product construction uses the jacobi Even Minus Square Product eq even Minus Product sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L395-L398
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaProduct.lean#L395-L398

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

theorem QEC.Coding.TannerLiftedProduct.jacobiEvenMinusSquareProduct_eq_evenMinusProduct_sq :
    jacobiEvenMinusSquareProduct = jacobiEvenMinusProduct ^ 2 := by sorry
