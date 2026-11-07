-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_sum_lowWeightSupport_pow_card_le_nonempty
-- name    : QEC.Coding.FiberBundle.RandomBase.sum_lowWeightSupport_pow_card_le_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:43:53.6452+00:00
-- url     : https://prove2.me/theorems/d726f141-81e7-4313-bdef-57b457314f23
-- title:
--   Random Base: sum low Weight Support pow card le nonempty
-- statement:
--   A low-weight-support sum is bounded by the sum over all nonempty supports.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L777-L799
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L777-L799

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.sum_lowWeightSupport_pow_card_le_nonempty
    (r : Nat) (t : ENNReal) :
    (∑ A : LowWeightSupport r, t ^ A.1.card) ≤
      ∑ A : NonemptyVariableSupport r, t ^ A.1.card := by sorry
