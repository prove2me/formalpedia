-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_usableHeavy_lightEdges_bound
-- name    : QEC.Coding.FiberBundle.TwistGraph.usableHeavy_lightEdges_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:47:30.643103+00:00
-- url     : https://prove2.me/theorems/c3860e69-1288-4782-b33f-726a9f49b6c6
-- title:
--   Twist Graph: usable Heavy light Edges bound
-- statement:
--   Summed trivial `2 * typeCount` bound over usable heavy layers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L552-L581
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L552-L581

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.usableHeavy_lightEdges_bound
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    100 *
        neighborEdgeCount twistSample
          (usableHeavyLayerSet Delta twistSample w)
          (lightLayerSet Delta w) ≤
      200 * typeCount *
        (usableHeavyLayerSet Delta twistSample w).card := by sorry
