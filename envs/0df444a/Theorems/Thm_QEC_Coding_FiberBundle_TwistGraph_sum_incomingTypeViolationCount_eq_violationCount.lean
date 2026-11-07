-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_incomingTypeViolationCount_eq_violationCount
-- name    : QEC.Coding.FiberBundle.TwistGraph.sum_incomingTypeViolationCount_eq_violationCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:45:23.26091+00:00
-- url     : https://prove2.me/theorems/6c9bc9f5-a0de-4040-ab55-5ba3fe1064dd
-- title:
--   Twist Graph: sum incoming Type Violation Count eq violation Count
-- statement:
--   Every violated check is counted once at the target of its twist edge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L222-L251
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L222-L251

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.sum_incomingTypeViolationCount_eq_violationCount
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    (∑ u : ZMod ell, ∑ τ : Fin typeCount,
      incomingTypeViolationCount baseSample twistSample w u τ) =
        violationCount baseSample twistSample w := by sorry
