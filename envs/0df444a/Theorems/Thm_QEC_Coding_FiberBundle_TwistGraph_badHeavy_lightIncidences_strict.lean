-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_badHeavy_lightIncidences_strict
-- name    : QEC.Coding.FiberBundle.TwistGraph.badHeavy_lightIncidences_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:47:27.737322+00:00
-- url     : https://prove2.me/theorems/3a439394-678b-4ff5-8b11-de37d27f7b3b
-- title:
--   Twist Graph: bad Heavy light Incidences strict
-- statement:
--   An unusable heavy layer has strictly less than `.99` of its `2 * typeCount`
--   incidences entering the light set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L486-L508
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L486-L508

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.badHeavy_lightIncidences_strict
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell)
    (hu : u ∈ badHeavyLayerSet Delta twistSample w) :
    100 *
        neighborIncidenceCount twistSample (lightLayerSet Delta w) u <
      198 * typeCount := by sorry
