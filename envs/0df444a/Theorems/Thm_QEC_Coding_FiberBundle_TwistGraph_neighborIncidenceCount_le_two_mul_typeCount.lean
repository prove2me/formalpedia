-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_neighborIncidenceCount_le_two_mul_typeCount
-- name    : QEC.Coding.FiberBundle.TwistGraph.neighborIncidenceCount_le_two_mul_typeCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:47:20.426421+00:00
-- url     : https://prove2.me/theorems/6809b50b-3362-4fff-985f-8c6b5049adaf
-- title:
--   Twist Graph: neighbor Incidence Count le two mul type Count
-- statement:
--   No target set can receive more than two incidences per type.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L422-L435
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L422-L435

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.neighborIncidenceCount_le_two_mul_typeCount
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (target : Finset (ZMod ell))
    (u : ZMod ell) :
    neighborIncidenceCount twistSample target u ≤ 2 * typeCount := by sorry
