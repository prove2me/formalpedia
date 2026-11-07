-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_dft_inNeighbor
-- name    : QEC.Coding.FiberBundle.TwistGraph.dft_inNeighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:52:10.467073+00:00
-- url     : https://prove2.me/theorems/7bfb1fca-fb27-4979-844a-2c26385e1304
-- title:
--   Twist Graph: dft in Neighbor
-- statement:
--   DFT of one inverse type translation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphFourier.lean#L86-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphFourier.lean#L86-L116

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod

theorem QEC.Coding.FiberBundle.TwistGraph.dft_inNeighbor
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount)
    (g : ZMod ell → Complex)
    (frequency : ZMod ell) :
    (∑ u : ZMod ell,
        ZMod.stdAddChar (-(u * frequency)) *
          g (inNeighbor twistSample τ u)) =
      ZMod.stdAddChar (-(step twistSample τ * frequency)) *
        ∑ u : ZMod ell,
          ZMod.stdAddChar (-(u * frequency)) * g u := by sorry
