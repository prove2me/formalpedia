-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_nine_typeCount_le_five_heavyIncidences_of_badNonheavy
-- name    : QEC.Coding.FiberBundle.TwistGraph.nine_typeCount_le_five_heavyIncidences_of_badNonheavy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:47:12.806505+00:00
-- url     : https://prove2.me/theorems/b13574ab-b3ff-474e-905a-6173e6fc9761
-- title:
--   Twist Graph: nine type Count le five heavy Incidences of bad Nonheavy
-- statement:
--   At an unusable nonheavy layer, at least `.9` of the `2 * typeCount`
--   incidences enter the heavy set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L255-L283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L255-L283

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.nine_typeCount_le_five_heavyIncidences_of_badNonheavy
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell)
    (hu : u ∈ badNonheavyLayerSet Delta twistSample w) :
    9 * typeCount ≤
      5 *
        neighborIncidenceCount twistSample
          (heavyLayerSet Delta w) u := by sorry
