-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_paritySign_row_sum
-- name    : QEC.Coding.FiberBundle.RandomBase.paritySign_row_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:35:45.747973+00:00
-- url     : https://prove2.me/theorems/fa9c6bcf-a22d-4653-99a0-303820255ae8
-- title:
--   Random Base: parity Sign row sum
-- statement:
--   The parity character factors over a selected variable subset.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L122-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L122-L130

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.paritySign_row_sum
    {r : Nat} (A : Finset (Fin (4 * r))) (row : RowSample r) :
    paritySign (∑ b ∈ A, cond (row b) (1 : ZMod 2) 0) =
      ∏ b ∈ A, signedBit (row b) := by sorry
