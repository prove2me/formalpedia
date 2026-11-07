-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_neighborIncidenceCount_union
-- name    : QEC.Coding.FiberBundle.TwistGraph.neighborIncidenceCount_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:47:00.573804+00:00
-- url     : https://prove2.me/theorems/a8a8ebe7-1250-48c7-87a7-876202976cf7
-- title:
--   Twist Graph: neighbor Incidence Count union
-- statement:
--   Neighbor-incidence counts add across disjoint target sets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L210-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L210-L238

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.neighborIncidenceCount_union
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (left right : Finset (ZMod ell))
    (hdisjoint : Disjoint left right)
    (u : ZMod ell) :
    neighborIncidenceCount twistSample (left ∪ right) u =
      neighborIncidenceCount twistSample left u +
        neighborIncidenceCount twistSample right u := by sorry
