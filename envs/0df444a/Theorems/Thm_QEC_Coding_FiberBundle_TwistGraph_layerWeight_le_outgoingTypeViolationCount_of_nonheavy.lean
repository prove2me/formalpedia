-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_layerWeight_le_outgoingTypeViolationCount_of_nonheavy
-- name    : QEC.Coding.FiberBundle.TwistGraph.layerWeight_le_outgoingTypeViolationCount_of_nonheavy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:45:35.9762+00:00
-- url     : https://prove2.me/theorems/26f8cefb-e255-48f3-b211-34816a8df868
-- title:
--   Twist Graph: layer Weight le outgoing Type Violation Count of nonheavy
-- statement:
--   A nonheavy-to-nonheavy outgoing incidence pays for the source weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L631-L675
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L631-L675

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.layerWeight_le_outgoingTypeViolationCount_of_nonheavy
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hLight : HasHHO20LightChecks Delta baseSample twistSample)
    (u : ZMod ell) (τ : Fin typeCount)
    (hu : u ∈ nonheavyLayerSet Delta w)
    (hv :
      outNeighbor twistSample τ u ∈ nonheavyLayerSet Delta w) :
    Delta * HammingWeight (layerWord w u) ≤
      100 * typeCount *
        outgoingTypeViolationCount baseSample twistSample w u τ := by sorry
