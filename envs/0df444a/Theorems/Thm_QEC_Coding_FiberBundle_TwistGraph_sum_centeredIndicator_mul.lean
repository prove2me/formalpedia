-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_centeredIndicator_mul
-- name    : QEC.Coding.FiberBundle.TwistGraph.sum_centeredIndicator_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:51:25.528768+00:00
-- url     : https://prove2.me/theorems/d92fc6ec-990d-4efe-b610-bfcaf1681e29
-- title:
--   Twist Graph: sum centered Indicator mul
-- statement:
--   Pairing a centered indicator with an arbitrary real function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L208-L224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L208-L224

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectral
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.sum_centeredIndicator_mul
    {ell : Nat}
    [NeZero ell]
    (vertices : Finset (ZMod ell))
    (h : ZMod ell → Real) :
    (∑ u : ZMod ell, centeredIndicator vertices u * h u) =
      ell * (∑ u ∈ vertices, h u) -
        vertices.card * ∑ u : ZMod ell, h u := by sorry
