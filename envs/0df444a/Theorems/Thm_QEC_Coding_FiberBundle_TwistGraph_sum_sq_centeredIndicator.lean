-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_sq_centeredIndicator
-- name    : QEC.Coding.FiberBundle.TwistGraph.sum_sq_centeredIndicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:50:37.526405+00:00
-- url     : https://prove2.me/theorems/8ec6f859-be20-4c66-9c9d-efee46f217c9
-- title:
--   Twist Graph: sum sq centered Indicator
-- statement:
--   The Twist Graph construction uses the sum sq centered Indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L82-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean#L82-L101

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectral
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators

theorem QEC.Coding.FiberBundle.TwistGraph.sum_sq_centeredIndicator
    {ell : Nat}
    [NeZero ell]
    (vertices : Finset (ZMod ell)) :
    (∑ u : ZMod ell, (centeredIndicator vertices u) ^ 2) =
      ell * vertices.card * (ell - vertices.card) := by sorry
