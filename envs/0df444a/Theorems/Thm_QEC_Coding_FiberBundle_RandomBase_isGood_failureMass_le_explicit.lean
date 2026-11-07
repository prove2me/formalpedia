-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_isGood_failureMass_le_explicit
-- name    : QEC.Coding.FiberBundle.RandomBase.isGood_failureMass_le_explicit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:09:18.897053+00:00
-- url     : https://prove2.me/theorems/b6db2f9d-817f-48dc-8434-980d67be6723
-- title:
--   Random Base: is Good failure Mass le explicit
-- statement:
--   Explicit combined failure bound for the construction-owned random base.
--   Every term on the right was derived from the Bernoulli sampler; none is a
--   caller-supplied rank, distance, or degree certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L1026-L1061
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L1026-L1061

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.isGood_failureMass_le_explicit
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample => IsGood (Delta := Delta) sample) ≤
      ENNReal.ofReal
          ((14 * r : Real) * Real.exp (-(Delta : Real) / 40000)) +
        ((1 + ENNReal.ofReal
          (Real.exp (-(Delta : Real) / 2))) ^ (3 * r) - 1 +
          (2 : ENNReal) ^ (3 * r) *
            (ENNReal.ofReal ((4 : Real) / 7)) ^ (4 * r)) +
        ((1 + ENNReal.ofReal
          (Real.exp (-(3 : Real) * Delta / 28))) ^ (4 * r) - 1 +
          ((3 : ENNReal) ^ ((4 * r) / 5) *
            ((4 : ENNReal) / 3) ^ (4 * r)) *
            (ENNReal.ofReal ((172 : Real) / 343)) ^ (3 * r)) := by sorry
