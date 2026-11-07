-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_neighborIncidenceCount_mul_layerWeight_le_incidentViolationCount
-- name    : QEC.Coding.FiberBundle.TwistGraph.neighborIncidenceCount_mul_layerWeight_le_incidentViolationCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:45:35.66492+00:00
-- url     : https://prove2.me/theorems/00459542-0946-4d43-a033-97d5ac93a22b
-- title:
--   Twist Graph: neighbor Incidence Count mul layer Weight le incident Violation Count
-- statement:
--   Summing the light-check lemma over all usable directed incidences at one
--   nonheavy layer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L728-L791
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L728-L791

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.neighborIncidenceCount_mul_layerWeight_le_incidentViolationCount
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hLight : HasHHO20LightChecks Delta baseSample twistSample)
    (u : ZMod ell)
    (hu : u ∈ nonheavyLayerSet Delta w) :
    neighborIncidenceCount twistSample (nonheavyLayerSet Delta w) u *
        (Delta * HammingWeight (layerWord w u)) ≤
      100 * typeCount *
        incidentViolationCount baseSample twistSample w u := by sorry
