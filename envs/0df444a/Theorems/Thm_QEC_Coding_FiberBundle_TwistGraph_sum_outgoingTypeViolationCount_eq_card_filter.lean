-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_outgoingTypeViolationCount_eq_card_filter
-- name    : QEC.Coding.FiberBundle.TwistGraph.sum_outgoingTypeViolationCount_eq_card_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:45:17.711209+00:00
-- url     : https://prove2.me/theorems/553a83bb-bb3c-40db-ac1c-a206a2907d80
-- title:
--   Twist Graph: sum outgoing Type Violation Count eq card filter
-- statement:
--   At a fixed layer, summing over types gives all outgoing violations.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L176-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L176-L191

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.sum_outgoingTypeViolationCount_eq_card_filter
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    (∑ τ : Fin typeCount,
      outgoingTypeViolationCount baseSample twistSample w u τ) =
      (Finset.univ.filter fun a : Fin (3 * r) =>
        checkSyndrome baseSample twistSample w u a ≠ 0).card := by sorry
