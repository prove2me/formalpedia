-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_nonheavyLayerSet_union_heavyLayerSet
-- name    : QEC.Coding.FiberBundle.TwistGraph.nonheavyLayerSet_union_heavyLayerSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:44:50.786272+00:00
-- url     : https://prove2.me/theorems/047d44d8-b47a-4e3a-8928-680bc5dc7ce9
-- title:
--   Twist Graph: nonheavy Layer Set union heavy Layer Set
-- statement:
--   Every layer is uniquely nonheavy or heavy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L382-L392
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L382-L392

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.nonheavyLayerSet_union_heavyLayerSet
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    nonheavyLayerSet Delta w ∪ heavyLayerSet Delta w = Finset.univ := by sorry
