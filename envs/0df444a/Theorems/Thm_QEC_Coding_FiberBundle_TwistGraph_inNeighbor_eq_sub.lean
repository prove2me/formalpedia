-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_eq_sub
-- name    : QEC.Coding.FiberBundle.TwistGraph.inNeighbor_eq_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:41:21.77921+00:00
-- url     : https://prove2.me/theorems/5008dcae-fe35-429e-b8af-610cc8225f5b
-- title:
--   Twist Graph: in Neighbor eq sub
-- statement:
--   The Twist Graph construction uses the in Neighbor eq sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L310-L316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L310-L316

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.inNeighbor_eq_sub
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) (u : ZMod ell) :
    inNeighbor sample τ u = u - step sample τ := by sorry
