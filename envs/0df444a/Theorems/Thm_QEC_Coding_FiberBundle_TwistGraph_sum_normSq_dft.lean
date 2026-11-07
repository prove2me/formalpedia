-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_normSq_dft
-- name    : QEC.Coding.FiberBundle.TwistGraph.sum_normSq_dft
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:52:13.29029+00:00
-- url     : https://prove2.me/theorems/1b2ede76-376d-4769-a8e0-1ccd3d0ff091
-- title:
--   Twist Graph: sum norm Sq dft
-- statement:
--   Squared `ℓ₂` norm Parseval identity for the unnormalized DFT.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphFourier.lean#L217-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphFourier.lean#L217-L228

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod

theorem QEC.Coding.FiberBundle.TwistGraph.sum_normSq_dft
    {ell : Nat}
    [NeZero ell]
    (g : ZMod ell → Complex) :
    (∑ frequency : ZMod ell,
        Complex.normSq (ZMod.dft g frequency)) =
      ell * ∑ u : ZMod ell, Complex.normSq (g u) := by sorry
