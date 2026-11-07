-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_usableHeavy_card_bound_of_lowerEdgeMixing
-- name    : QEC.Coding.FiberBundle.TwistGraph.usableHeavy_card_bound_of_lowerEdgeMixing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:47:45.408972+00:00
-- url     : https://prove2.me/theorems/82f19f05-128f-41ec-a0e7-91ad6e337b72
-- title:
--   Twist Graph: usable Heavy card bound of lower Edge Mixing
-- statement:
--   The lower `.999` oriented-edge estimate implies that at least `.9 |H|`
--   heavy layers satisfy the two-sided `.98 typeCount` condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L587-L696
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L587-L696

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.usableHeavy_card_bound_of_lowerEdgeMixing
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hLower :
      1998 * typeCount * (heavyLayerSet Delta w).card ≤
        1000 *
          neighborEdgeCount twistSample
            (heavyLayerSet Delta w) (lightLayerSet Delta w)) :
    9 * (heavyLayerSet Delta w).card ≤
      10 * (usableHeavyLayerSet Delta twistSample w).card := by sorry
