-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_parityProbabilityBase_veryLarge_le
-- name    : QEC.Coding.FiberBundle.RandomBase.parityProbabilityBase_veryLarge_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:43:41.647389+00:00
-- url     : https://prove2.me/theorems/22bdfee1-760e-4344-935f-d8cf14f059da
-- title:
--   Random Base: parity Probability Base very Large le
-- statement:
--   Once `p w ≥ 3`, the parity-zero base is at most `172/343`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L511-L524
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L511-L524

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.parityProbabilityBase_veryLarge_le
    (p : Real) (w : Nat) (hpHalf : p ≤ 1 / 2)
    (hlarge : 3 ≤ p * w) :
    (1 + (1 - 2 * p) ^ w) / 2 ≤ (172 : Real) / 343 := by sorry
