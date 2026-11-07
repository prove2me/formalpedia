-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_incomingTypeViolationCount_eq_outgoing_inNeighbor
-- name    : QEC.Coding.FiberBundle.TwistGraph.incomingTypeViolationCount_eq_outgoing_inNeighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:45:12.312245+00:00
-- url     : https://prove2.me/theorems/64135af5-793f-470c-a243-fe8b375c7a56
-- title:
--   Twist Graph: incoming Type Violation Count eq outgoing in Neighbor
-- statement:
--   An incoming count is the outgoing count at the unique source layer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L209-L219
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L209-L219

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.incomingTypeViolationCount_eq_outgoing_inNeighbor
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) (τ : Fin typeCount) :
    incomingTypeViolationCount baseSample twistSample w u τ =
      outgoingTypeViolationCount baseSample twistSample w
        (inNeighbor twistSample τ u) τ := by sorry
