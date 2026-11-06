-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_sum_nonemptyVariableSupport_pow_card
-- name    : QEC.Coding.FiberBundle.RandomBase.sum_nonemptyVariableSupport_pow_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:44:14.464181+00:00
-- url     : https://prove2.me/theorems/3a14287c-af43-49e4-98ff-72c622c3faaa
-- title:
--   Random Base: sum nonempty Variable Support pow card
-- statement:
--   Exact binomial sum over all nonempty variable supports.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L802-L807
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L802-L807

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.sum_nonemptyVariableSupport_pow_card
    (r : Nat) (t : ENNReal) :
    (∑ A : NonemptyVariableSupport r, t ^ A.1.card) =
      (1 + t) ^ (4 * r) - 1 := by sorry
