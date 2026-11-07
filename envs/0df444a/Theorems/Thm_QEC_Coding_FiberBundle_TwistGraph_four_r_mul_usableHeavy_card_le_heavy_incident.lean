-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_four_r_mul_usableHeavy_card_le_heavy_incident
-- name    : QEC.Coding.FiberBundle.TwistGraph.four_r_mul_usableHeavy_card_le_heavy_incident
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:46:37.102242+00:00
-- url     : https://prove2.me/theorems/fd4b1f17-ad9d-4a48-a0a0-3fb70c846c0c
-- title:
--   Twist Graph: four r mul usable Heavy card le heavy incident
-- statement:
--   Aggregate `.01n` payment from all usable heavy layers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L1075-L1110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L1075-L1110

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.four_r_mul_usableHeavy_card_le_heavy_incident
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hHeavy : HasHHO20HeavyChecks Delta baseSample twistSample) :
    (4 * r) * (usableHeavyLayerSet Delta twistSample w).card ≤
      100 *
        (∑ u ∈ heavyLayerSet Delta w,
          incidentViolationCount baseSample twistSample w u) := by sorry
