-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_outNeighbor
-- name    : QEC.Coding.FiberBundle.TwistGraph.inNeighbor_outNeighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:41:45.986732+00:00
-- url     : https://prove2.me/theorems/f92dea5f-5103-482f-a01e-916dbfe5c53d
-- title:
--   Twist Graph: in Neighbor out Neighbor
-- statement:
--   The Twist Graph construction uses the in Neighbor out Neighbor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L319-L325
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L319-L325

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.inNeighbor_outNeighbor
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) (u : ZMod ell) :
    inNeighbor sample τ (outNeighbor sample τ u) = u := by sorry
