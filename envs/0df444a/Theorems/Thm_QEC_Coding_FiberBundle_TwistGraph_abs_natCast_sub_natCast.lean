-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_abs_natCast_sub_natCast
-- name    : QEC.Coding.FiberBundle.TwistGraph.abs_natCast_sub_natCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:51:42.749318+00:00
-- url     : https://prove2.me/theorems/a80c5d28-c3e2-4224-9a69-63d68f105712
-- title:
--   Twist Graph: abs nat Cast sub nat Cast
-- statement:
--   Real absolute difference of natural casts is the cast of `Nat.dist`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L282-L292
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L282-L292

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectral
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.abs_natCast_sub_natCast (a b : Nat) :
    |(a : Real) - b| = Nat.dist a b := by sorry
