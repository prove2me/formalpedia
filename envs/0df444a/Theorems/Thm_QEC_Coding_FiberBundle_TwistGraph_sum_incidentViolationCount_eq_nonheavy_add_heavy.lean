-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_incidentViolationCount_eq_nonheavy_add_heavy
-- name    : QEC.Coding.FiberBundle.TwistGraph.sum_incidentViolationCount_eq_nonheavy_add_heavy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:46:20.943785+00:00
-- url     : https://prove2.me/theorems/5aa77f74-451b-41e5-acb5-c78850bc82e2
-- title:
--   Twist Graph: sum incident Violation Count eq nonheavy add heavy
-- statement:
--   Incident violations split exactly across nonheavy and heavy layers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L926-L941
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L926-L941

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.sum_incidentViolationCount_eq_nonheavy_add_heavy
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    (∑ u : ZMod ell,
      incidentViolationCount baseSample twistSample w u) =
      (∑ u ∈ nonheavyLayerSet Delta w,
        incidentViolationCount baseSample twistSample w u) +
      (∑ u ∈ heavyLayerSet Delta w,
        incidentViolationCount baseSample twistSample w u) := by sorry
