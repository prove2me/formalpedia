-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_dft_parseval
-- name    : QEC.Coding.FiberBundle.TwistGraph.dft_parseval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:52:11.045827+00:00
-- url     : https://prove2.me/theorems/ae9e0433-4d1d-4749-9623-c7fae49b2ad0
-- title:
--   Twist Graph: dft parseval
-- statement:
--   Parseval identity for the unnormalized DFT on `ZMod ell`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphFourier.lean#L151-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphFourier.lean#L151-L214

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod

theorem QEC.Coding.FiberBundle.TwistGraph.dft_parseval
    {ell : Nat}
    [NeZero ell]
    (f g : ZMod ell → Complex) :
    (∑ frequency : ZMod ell,
        star (ZMod.dft f frequency) *
          ZMod.dft g frequency) =
      ell * ∑ u : ZMod ell, star (f u) * g u := by sorry
