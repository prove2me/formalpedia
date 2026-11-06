-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_violationCount_eq_sum_checkColumn
-- name    : QEC.Coding.FiberBundle.TwistGraph.violationCount_eq_sum_checkColumn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:46:25.846768+00:00
-- url     : https://prove2.me/theorems/83b682cb-8e0d-45a8-9c7c-11eec7978676
-- title:
--   Twist Graph: violation Count eq sum check Column
-- statement:
--   Violation count is the sum of the per-base-check column weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L448-L463
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraph.lean#L448-L463

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.violationCount_eq_sum_checkColumn
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    violationCount baseSample twistSample w =
      ∑ a : Fin (3 * r),
        HammingWeight (checkColumn baseSample twistSample w a) := by sorry
