-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_integral_row_signedBit_product
-- name    : QEC.Coding.FiberBundle.RandomBase.integral_row_signedBit_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:35:53.666201+00:00
-- url     : https://prove2.me/theorems/aa138e48-f3f4-4616-a212-e9dd8eaf3ff7
-- title:
--   Random Base: integral row signed Bit product
-- statement:
--   The signed expectation over a selected variable subset factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L155-L177
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L155-L177

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.integral_row_signedBit_product
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) :
    ∫ row, (∏ b ∈ A, signedBit (row b)) ∂
        (rowDistribution r Delta hDelta).toMeasure =
      (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^ A.card := by sorry
