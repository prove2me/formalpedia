-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_eq_add
-- name    : QEC.Coding.FiberBundle.TwistGraph.outNeighbor_eq_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:41:06.960947+00:00
-- url     : https://prove2.me/theorems/df7c80d8-5fe3-468c-a7b4-e2e4f5d72475
-- title:
--   Twist Graph: out Neighbor eq add
-- statement:
--   The Twist Graph construction uses the out Neighbor eq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L301-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L301-L307

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.outNeighbor_eq_add
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) (u : ZMod ell) :
    outNeighbor sample τ u = u + step sample τ := by sorry

attribute [defeq] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_eq_add
