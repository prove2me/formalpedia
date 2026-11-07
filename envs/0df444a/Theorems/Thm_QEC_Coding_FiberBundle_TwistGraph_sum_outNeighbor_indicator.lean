-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_outNeighbor_indicator
-- name    : QEC.Coding.FiberBundle.TwistGraph.sum_outNeighbor_indicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:51:06.734294+00:00
-- url     : https://prove2.me/theorems/3ba35917-b977-43b6-8441-129fdaf98990
-- title:
--   Twist Graph: sum out Neighbor indicator
-- statement:
--   A translated membership indicator has the same total as the set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L104-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L104-L120

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectral
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.sum_outNeighbor_indicator
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount)
    (vertices : Finset (ZMod ell)) :
    (∑ u : ZMod ell,
        if outNeighbor twistSample τ u ∈ vertices then 1 else 0) =
      vertices.card := by sorry
