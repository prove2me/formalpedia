-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_complexNeighborSum_ofReal
-- name    : QEC.Coding.FiberBundle.TwistGraph.complexNeighborSum_ofReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:52:40.172776+00:00
-- url     : https://prove2.me/theorems/1aed4a22-6f65-4e6e-b2d4-1096f06f2ffa
-- title:
--   Twist Graph: complex Neighbor Sum of Real
-- statement:
--   Complex adjacency agrees with the real adjacency on real-valued inputs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphFourier.lean#L305-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphFourier.lean#L305-L313

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod

theorem QEC.Coding.FiberBundle.TwistGraph.complexNeighborSum_ofReal
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (g : ZMod ell → Real)
    (u : ZMod ell) :
    complexNeighborSum twistSample (fun v => (g v : Complex)) u =
      (undirectedNeighborSum twistSample g u : Complex) := by sorry
