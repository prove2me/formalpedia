-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_conj_stdAddChar_neg
-- name    : QEC.Coding.FiberBundle.TwistGraph.conj_stdAddChar_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:51:42.674998+00:00
-- url     : https://prove2.me/theorems/57664298-e05b-4826-94c9-f2f9671f42ba
-- title:
--   Twist Graph: conj std Add Char neg
-- statement:
--   Conjugating the negative standard character recovers the character.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphFourier.lean#L141-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphFourier.lean#L141-L148

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod

theorem QEC.Coding.FiberBundle.TwistGraph.conj_stdAddChar_neg
    {ell : Nat}
    [NeZero ell]
    (x : ZMod ell) :
    star (ZMod.stdAddChar (-x)) =
      ZMod.stdAddChar x := by sorry
