-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_isFullyGood_failureMass_le_explicit
-- name    : QEC.Coding.FiberBundle.RandomBase.isFullyGood_failureMass_le_explicit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:59:35.793205+00:00
-- url     : https://prove2.me/theorems/ff6936ce-30e0-452f-9a96-452cf86c3a1c
-- title:
--   Random Base: is Fully Good failure Mass le explicit
-- statement:
--   Explicit combined failure bound including random-base small-set expansion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1305-L1338
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1305-L1338

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.isFullyGood_failureMass_le_explicit
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample => IsFullyGood (Delta := Delta) sample) ≤
      (ENNReal.ofReal
          ((14 * r : Real) * Real.exp (-(Delta : Real) / 40000)) +
        ((1 + ENNReal.ofReal
          (Real.exp (-(Delta : Real) / 2))) ^ (3 * r) - 1 +
          (2 : ENNReal) ^ (3 * r) *
            (ENNReal.ofReal ((4 : Real) / 7)) ^ (4 * r)) +
        ((1 + ENNReal.ofReal
          (Real.exp (-(3 : Real) * Delta / 28))) ^ (4 * r) - 1 +
          ((3 : ENNReal) ^ ((4 * r) / 5) *
            ((4 : ENNReal) / 3) ^ (4 * r)) *
            (ENNReal.ofReal ((172 : Real) / 343)) ^ (3 * r))) +
      ((1 + ENNReal.ofReal
        (Real.exp (-(Delta : Real) / 1000))) ^ (3 * r) - 1) := by sorry
