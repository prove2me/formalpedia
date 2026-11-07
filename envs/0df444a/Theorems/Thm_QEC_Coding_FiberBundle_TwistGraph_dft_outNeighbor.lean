-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_dft_outNeighbor
-- name    : QEC.Coding.FiberBundle.TwistGraph.dft_outNeighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:51:56.463204+00:00
-- url     : https://prove2.me/theorems/b2b9e8af-d35c-4ce6-acbc-657dd8d6370c
-- title:
--   Twist Graph: dft out Neighbor
-- statement:
--   DFT of one forward type translation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphFourier.lean#L53-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphFourier.lean#L53-L83

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod

theorem QEC.Coding.FiberBundle.TwistGraph.dft_outNeighbor
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount)
    (g : ZMod ell → Complex)
    (frequency : ZMod ell) :
    (∑ u : ZMod ell,
        ZMod.stdAddChar (-(u * frequency)) *
          g (outNeighbor twistSample τ u)) =
      ZMod.stdAddChar (step twistSample τ * frequency) *
        ∑ u : ZMod ell,
          ZMod.stdAddChar (-(u * frequency)) * g u := by sorry
