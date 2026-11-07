-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_badHeavy_lightEdges_bound
-- name    : QEC.Coding.FiberBundle.TwistGraph.badHeavy_lightEdges_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:47:23.477355+00:00
-- url     : https://prove2.me/theorems/735cfdf3-7f99-4a3e-978b-08b682ef8a0c
-- title:
--   Twist Graph: bad Heavy light Edges bound
-- statement:
--   Summed strict light-incidence bound over unusable heavy layers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L511-L549
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L511-L549

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.badHeavy_lightEdges_bound
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    100 *
        neighborEdgeCount twistSample
          (badHeavyLayerSet Delta twistSample w)
          (lightLayerSet Delta w) +
        (badHeavyLayerSet Delta twistSample w).card ≤
      198 * typeCount *
        (badHeavyLayerSet Delta twistSample w).card := by sorry
