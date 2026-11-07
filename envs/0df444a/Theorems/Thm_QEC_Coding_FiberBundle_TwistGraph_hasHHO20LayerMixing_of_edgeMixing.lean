-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_hasHHO20LayerMixing_of_edgeMixing
-- name    : QEC.Coding.FiberBundle.TwistGraph.hasHHO20LayerMixing_of_edgeMixing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:48:16.623258+00:00
-- url     : https://prove2.me/theorems/9b9ea471-57ef-4d80-b1ba-34aeed89c4bf
-- title:
--   Twist Graph: has HHO20 Layer Mixing of edge Mixing
-- statement:
--   The two edge-mixing estimates imply the word-indexed layer event.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L699-L714
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L699-L714

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.hasHHO20LayerMixing_of_edgeMixing
    {r typeCount ell : Nat}
    [NeZero r] [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hEdge : HasHHO20EdgeMixing Delta twistSample) :
    HasHHO20LayerMixing Delta twistSample := by sorry
