-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_centeredIndicator_eq_mul_indicator_sub_card
-- name    : QEC.Coding.FiberBundle.TwistGraph.centeredIndicator_eq_mul_indicator_sub_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:50:17.352203+00:00
-- url     : https://prove2.me/theorems/db54e4e7-097e-4c31-9187-fcfd246639a2
-- title:
--   Twist Graph: centered Indicator eq mul indicator sub card
-- statement:
--   Pointwise algebraic form of the centered indicator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L174-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L174-L183

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectral
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.centeredIndicator_eq_mul_indicator_sub_card
    {ell : Nat}
    (vertices : Finset (ZMod ell))
    (u : ZMod ell) :
    centeredIndicator vertices u =
      ell * (if u ∈ vertices then (1 : Real) else 0) -
        vertices.card := by sorry
