-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outgoingTypeViolationCount_eq_card_filter
-- name    : QEC.Coding.FiberBundle.TwistGraph.outgoingTypeViolationCount_eq_card_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:45:22.203576+00:00
-- url     : https://prove2.me/theorems/89ab28b1-d598-43b2-8e3e-d790844362ff
-- title:
--   Twist Graph: outgoing Type Violation Count eq card filter
-- statement:
--   The outgoing type count is the corresponding fiber of the global violated
--   checks at source layer `u`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L148-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean#L148-L173

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.outgoingTypeViolationCount_eq_card_filter
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) (τ : Fin typeCount) :
    outgoingTypeViolationCount baseSample twistSample w u τ =
      (Finset.univ.filter fun a : Fin (3 * r) =>
        RandomTwist.checkType typeCount a = τ ∧
          checkSyndrome baseSample twistSample w u a ≠ 0).card := by sorry
