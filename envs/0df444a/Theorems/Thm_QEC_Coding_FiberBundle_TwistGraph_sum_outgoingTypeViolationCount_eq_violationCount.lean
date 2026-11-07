-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_outgoingTypeViolationCount_eq_violationCount
-- name    : QEC.Coding.FiberBundle.TwistGraph.sum_outgoingTypeViolationCount_eq_violationCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:44:57.190055+00:00
-- url     : https://prove2.me/theorems/598be50e-ca96-4e2f-a518-fd6f3a2f7d26
-- title:
--   Twist Graph: sum outgoing Type Violation Count eq violation Count
-- statement:
--   Every violated check is counted once at the source of its twist edge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L194-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L194-L206

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.sum_outgoingTypeViolationCount_eq_violationCount
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    (∑ u : ZMod ell, ∑ τ : Fin typeCount,
      outgoingTypeViolationCount baseSample twistSample w u τ) =
        violationCount baseSample twistSample w := by sorry
