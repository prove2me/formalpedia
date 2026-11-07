-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_card_light_add_medium_add_heavy
-- name    : QEC.Coding.FiberBundle.TwistGraph.card_light_add_medium_add_heavy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:46:38.67532+00:00
-- url     : https://prove2.me/theorems/82b20635-4fc8-4eb2-9928-b3fc9f335a6c
-- title:
--   Twist Graph: card light add medium add heavy
-- statement:
--   The three HHO20 layer classes contain every layer exactly once.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L30-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean#L30-L58

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.card_light_add_medium_add_heavy
    {r ell : Nat}
    [NeZero r] [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    (lightLayerSet Delta w).card +
        (mediumLayerSet Delta w).card +
        (heavyLayerSet Delta w).card =
      ell := by sorry
