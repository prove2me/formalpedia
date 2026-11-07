-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_four_r_le_100_mul_incidentViolationCount_of_usableHeavy
-- name    : QEC.Coding.FiberBundle.TwistGraph.four_r_le_100_mul_incidentViolationCount_of_usableHeavy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:45:42.994455+00:00
-- url     : https://prove2.me/theorems/f89bb865-a66b-4c09-900b-87986823f505
-- title:
--   Twist Graph: four r le 100 mul incident Violation Count of usable Heavy
-- statement:
--   The local `.01n` bound for a usable heavy layer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L837-L880
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L837-L880

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.four_r_le_100_mul_incidentViolationCount_of_usableHeavy
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hHeavy : HasHHO20HeavyChecks Delta baseSample twistSample)
    (u : ZMod ell)
    (hu : u ∈ usableHeavyLayerSet Delta twistSample w) :
    4 * r ≤
      100 * incidentViolationCount baseSample twistSample w u := by sorry
