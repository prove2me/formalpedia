-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_incidentViolationCount_eq_two_mul_violationCount
-- name    : QEC.Coding.FiberBundle.TwistGraph.sum_incidentViolationCount_eq_two_mul_violationCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:46:09.543206+00:00
-- url     : https://prove2.me/theorems/73c471df-31db-4b70-a24b-710b81abad43
-- title:
--   Twist Graph: sum incident Violation Count eq two mul violation Count
-- statement:
--   The exact double-counting identity used in HHO20 `thm:ltc`: each violated
--   twist check is incident to its source and target layers, and hence is counted
--   exactly twice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L258-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L258-L270

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.sum_incidentViolationCount_eq_two_mul_violationCount
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    (∑ u : ZMod ell,
      incidentViolationCount baseSample twistSample w u) =
        2 * violationCount baseSample twistSample w := by sorry
