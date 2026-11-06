-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_ne
-- name    : QEC.Coding.FiberBundle.TwistGraph.outNeighbor_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:46:07.354451+00:00
-- url     : https://prove2.me/theorems/dcb30f5e-9aa0-45e3-b21e-25612fe8c91e
-- title:
--   Twist Graph: out Neighbor ne
-- statement:
--   The sampled directed twist graph has no self-loop.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L337-L346
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L337-L346

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.outNeighbor_ne
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) (u : ZMod ell) :
    outNeighbor sample τ u ≠ u := by sorry
