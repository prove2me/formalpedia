-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_disjoint_nonheavyLayerSet_heavyLayerSet
-- name    : QEC.Coding.FiberBundle.TwistGraph.disjoint_nonheavyLayerSet_heavyLayerSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:45:04.651203+00:00
-- url     : https://prove2.me/theorems/5e5d9eb7-1bbf-43a1-bf20-30da4efe4031
-- title:
--   Twist Graph: disjoint nonheavy Layer Set heavy Layer Set
-- statement:
--   The Twist Graph construction uses the disjoint nonheavy Layer Set heavy Layer Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L394-L405
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L394-L405

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.disjoint_nonheavyLayerSet_heavyLayerSet
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Disjoint (nonheavyLayerSet Delta w) (heavyLayerSet Delta w) := by sorry
