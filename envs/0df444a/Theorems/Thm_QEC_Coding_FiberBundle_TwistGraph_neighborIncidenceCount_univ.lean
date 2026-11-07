-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_neighborIncidenceCount_univ
-- name    : QEC.Coding.FiberBundle.TwistGraph.neighborIncidenceCount_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:46:48.297138+00:00
-- url     : https://prove2.me/theorems/a4fe4e5c-1df2-49a1-b82f-00edadcaca08
-- title:
--   Twist Graph: neighbor Incidence Count univ
-- statement:
--   Every layer has exactly two directed incidences per type.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L200-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L200-L207

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.neighborIncidenceCount_univ
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : ZMod ell) :
    neighborIncidenceCount twistSample Finset.univ u =
      2 * typeCount := by sorry
