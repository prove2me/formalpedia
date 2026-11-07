-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_hasHHO20SquaredExpanderMixing_of_operatorMixing
-- name    : QEC.Coding.FiberBundle.TwistGraph.hasHHO20SquaredExpanderMixing_of_operatorMixing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:55:46.029004+00:00
-- url     : https://prove2.me/theorems/4e3b457c-d731-4d4a-bf80-da62e82dd55e
-- title:
--   Twist Graph: has HHO20 Squared Expander Mixing of operator Mixing
-- statement:
--   The concrete nonconstant operator bound implies the integer-cleared squared
--   Expander Mixing event consumed by `TwistGraphSpectral`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L298-L362
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L298-L362

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectral
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.hasHHO20SquaredExpanderMixing_of_operatorMixing
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hOperator : HasHHO20OperatorMixing twistSample) :
    HasHHO20SquaredExpanderMixing twistSample := by sorry
