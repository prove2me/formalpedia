-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_linearDistance_failureMass_le_exact_sum
-- name    : QEC.Coding.FiberBundle.RandomBase.linearDistance_failureMass_le_exact_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:44:38.944236+00:00
-- url     : https://prove2.me/theorems/a0778668-88cf-43ab-b883-0f9783fdb9c9
-- title:
--   Random Base: linear Distance failure Mass le exact sum
-- statement:
--   Exact low-support union bound for failure of the source's classical
--   linear-distance event.  The next analytic layer estimates this finite sum;
--   the reduction itself makes no counting assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L843-L864
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L843-L864

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.linearDistance_failureMass_le_exact_sum
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (@HasLinearDistance r) ≤
      ∑ A : LowWeightSupport r,
        (ENNReal.ofReal
          ((1 +
            (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^
              A.1.card) / 2)) ^ (3 * r) := by sorry
