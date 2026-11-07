-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_nonheavy_weight_le_incident_add_heavy_error
-- name    : QEC.Coding.FiberBundle.TwistGraph.nonheavy_weight_le_incident_add_heavy_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:46:44.791525+00:00
-- url     : https://prove2.me/theorems/862d38f4-c649-4187-8ac9-5d5da77348b6
-- title:
--   Twist Graph: nonheavy weight le incident add heavy error
-- statement:
--   Aggregate form of HHO20 equation `ineq:mainsub`, with all decimals cleared:
--   `Delta * W_nonheavy ≤ 500 I_nonheavy + 5 n |H|`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L982-L1072
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L982-L1072

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.nonheavy_weight_le_incident_add_heavy_error
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hLight : HasHHO20LightChecks Delta baseSample twistSample)
    (hBad :
      4 * (badNonheavyLayerSet Delta twistSample w).card ≤
        5 * (heavyLayerSet Delta w).card) :
    Delta *
        (∑ u ∈ nonheavyLayerSet Delta w,
          HammingWeight (layerWord w u)) ≤
      500 *
          (∑ u ∈ nonheavyLayerSet Delta w,
            incidentViolationCount baseSample twistSample w u) +
        5 * (4 * r) * (heavyLayerSet Delta w).card := by sorry
