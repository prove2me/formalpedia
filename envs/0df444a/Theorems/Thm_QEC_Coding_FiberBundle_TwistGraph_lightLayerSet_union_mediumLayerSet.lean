-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_lightLayerSet_union_mediumLayerSet
-- name    : QEC.Coding.FiberBundle.TwistGraph.lightLayerSet_union_mediumLayerSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:46:00.595787+00:00
-- url     : https://prove2.me/theorems/e7fa745d-0ca7-4369-8505-b01e959c06de
-- title:
--   Twist Graph: light Layer Set union medium Layer Set
-- statement:
--   The light/medium union is exactly the set of nonheavy layers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L367-L379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L367-L379

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.lightLayerSet_union_mediumLayerSet
    {r ell : Nat}
    [NeZero r] [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    lightLayerSet Delta w ∪ mediumLayerSet Delta w =
      nonheavyLayerSet Delta w := by sorry
