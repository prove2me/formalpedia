-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_layerWeight_le_500_mul_incidentViolationCount_of_usableNonheavy
-- name    : QEC.Coding.FiberBundle.TwistGraph.layerWeight_le_500_mul_incidentViolationCount_of_usableNonheavy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:45:40.781059+00:00
-- url     : https://prove2.me/theorems/6e3e7366-4a07-4a24-b9c3-9a109229f4e4
-- title:
--   Twist Graph: layer Weight le 500 mul incident Violation Count of usable Nonheavy
-- statement:
--   The local `.002 Delta` bound for a usable nonheavy layer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L794-L834
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L794-L834

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.layerWeight_le_500_mul_incidentViolationCount_of_usableNonheavy
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hLight : HasHHO20LightChecks Delta baseSample twistSample)
    (u : ZMod ell)
    (hu : u ∈ usableNonheavyLayerSet Delta twistSample w) :
    Delta * HammingWeight (layerWord w u) ≤
      500 * incidentViolationCount baseSample twistSample w u := by sorry
