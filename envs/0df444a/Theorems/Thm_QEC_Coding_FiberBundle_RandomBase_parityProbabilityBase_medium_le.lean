-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_parityProbabilityBase_medium_le
-- name    : QEC.Coding.FiberBundle.RandomBase.parityProbabilityBase_medium_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:43:00.828756+00:00
-- url     : https://prove2.me/theorems/e1187847-54a6-4e95-9b3d-c9c730af02cc
-- title:
--   Random Base: parity Probability Base medium le
-- statement:
--   On `0 ≤ p w ≤ 3`, the parity-zero base is at most `exp(-p w / 7)`.
--   The rational constant is deliberately conservative but remains strong enough
--   for the later low-weight union bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L474-L496
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L474-L496

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.parityProbabilityBase_medium_le
    (p : Real) (w : Nat) (hp0 : 0 ≤ p) (hpHalf : p ≤ 1 / 2)
    (hmedium : p * w ≤ 3) :
    (1 + (1 - 2 * p) ^ w) / 2 ≤
      Real.exp (-(p * w) / 7) := by sorry
