-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_nine_typeCount_mul_badNonheavy_card_le_five_edges
-- name    : QEC.Coding.FiberBundle.TwistGraph.nine_typeCount_mul_badNonheavy_card_le_five_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:46:55.760207+00:00
-- url     : https://prove2.me/theorems/1e714497-c6f0-463e-95c7-18664ef8023c
-- title:
--   Twist Graph: nine type Count mul bad Nonheavy card le five edges
-- statement:
--   Summed `.9` heavy-neighbor bound over all unusable nonheavy layers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L286-L318
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L286-L318

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.nine_typeCount_mul_badNonheavy_card_le_five_edges
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    9 * typeCount *
        (badNonheavyLayerSet Delta twistSample w).card ≤
      5 *
        neighborEdgeCount twistSample
          (badNonheavyLayerSet Delta twistSample w)
          (heavyLayerSet Delta w) := by sorry
