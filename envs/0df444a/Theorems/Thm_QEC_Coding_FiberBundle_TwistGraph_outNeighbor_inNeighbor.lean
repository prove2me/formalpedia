-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_inNeighbor
-- name    : QEC.Coding.FiberBundle.TwistGraph.outNeighbor_inNeighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:41:54.400552+00:00
-- url     : https://prove2.me/theorems/2b38706a-97d1-4ffc-9301-1a123de608ec
-- title:
--   Twist Graph: out Neighbor in Neighbor
-- statement:
--   The Twist Graph construction uses the out Neighbor in Neighbor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L328-L334
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L328-L334

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.outNeighbor_inNeighbor
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) (u : ZMod ell) :
    outNeighbor sample τ (inNeighbor sample τ u) = u := by sorry
