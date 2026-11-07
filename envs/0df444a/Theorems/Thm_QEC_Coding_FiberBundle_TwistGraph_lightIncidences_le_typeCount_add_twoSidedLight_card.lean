-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_lightIncidences_le_typeCount_add_twoSidedLight_card
-- name    : QEC.Coding.FiberBundle.TwistGraph.lightIncidences_le_typeCount_add_twoSidedLight_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:47:19.556199+00:00
-- url     : https://prove2.me/theorems/39e0830c-f79c-4395-8a43-82e8fec54064
-- title:
--   Twist Graph: light Incidences le type Count add two Sided Light card
-- statement:
--   Light-neighbor incidences are at most one per type, plus one extra precisely
--   for each two-sided-light type.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L441-L480
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L441-L480

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.lightIncidences_le_typeCount_add_twoSidedLight_card
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    neighborIncidenceCount twistSample (lightLayerSet Delta w) u ≤
      typeCount +
        (twoSidedLightTypeSet Delta twistSample w u).card := by sorry
