-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_linearDistance_failureMass_le_split
-- name    : QEC.Coding.FiberBundle.RandomBase.linearDistance_failureMass_le_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:44:19.576852+00:00
-- url     : https://prove2.me/theorems/fbc96a69-f71e-4a62-a742-416fc83a1c8c
-- title:
--   Random Base: linear Distance failure Mass le split
-- statement:
--   Fully counted small/very-large split for the HHO20 classical-distance event.
--
--   The first term sums the geometric estimate over every nonempty support.  The
--   second uses the rational `1/3` weighted count of all supports below `0.2n`
--   and the `172/343` parity base valid once `Delta |A| ≥ 12r`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L873-L931
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L873-L931

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.linearDistance_failureMass_le_split
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (@HasLinearDistance r) ≤
      (1 + ENNReal.ofReal
        (Real.exp (-(3 : Real) * Delta / 28))) ^ (4 * r) - 1 +
      ((3 : ENNReal) ^ ((4 * r) / 5) *
        ((4 : ENNReal) / 3) ^ (4 * r)) *
        (ENNReal.ofReal ((172 : Real) / 343)) ^ (3 * r) := by sorry
