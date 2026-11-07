-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_neighborIncidenceCount
-- name    : QEC.Coding.FiberBundle.TwistGraph.sum_neighborIncidenceCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:51:22.786308+00:00
-- url     : https://prove2.me/theorems/9ce38eb1-919c-40ff-beb2-50ef43e33573
-- title:
--   Twist Graph: sum neighbor Incidence Count
-- statement:
--   Every target vertex receives exactly `2 * typeCount` incidences in total.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L142-L171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L142-L171

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectral
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.sum_neighborIncidenceCount
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (vertices : Finset (ZMod ell)) :
    (∑ u : ZMod ell,
        neighborIncidenceCount twistSample vertices u) =
      2 * typeCount * vertices.card := by sorry
