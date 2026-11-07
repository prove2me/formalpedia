-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_inNeighbor_indicator
-- name    : QEC.Coding.FiberBundle.TwistGraph.sum_inNeighbor_indicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:51:23.405208+00:00
-- url     : https://prove2.me/theorems/5ac4071d-3d30-4545-8430-7112f5f6ad74
-- title:
--   Twist Graph: sum in Neighbor indicator
-- statement:
--   The inverse translated membership indicator has the same total.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L123-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L123-L139

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectral
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.sum_inNeighbor_indicator
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount)
    (vertices : Finset (ZMod ell)) :
    (∑ u : ZMod ell,
        if inNeighbor twistSample τ u ∈ vertices then 1 else 0) =
      vertices.card := by sorry
