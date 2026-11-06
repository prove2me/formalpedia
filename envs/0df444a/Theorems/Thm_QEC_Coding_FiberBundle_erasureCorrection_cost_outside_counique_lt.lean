-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_erasureCorrection_cost_outside_counique_lt
-- name    : QEC.Coding.FiberBundle.erasureCorrection_cost_outside_counique_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:56:47.429406+00:00
-- url     : https://prove2.me/theorems/12a21875-d7e8-49dc-bf99-dfbf546651f2
-- title:
--   Fiber Bundle: erasure Correction cost outside counique lt
-- statement:
--   For a `> 4/5` counique check, correction cost outside its counique variables
--   is strictly smaller than the saving on those variables.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1530-L1592
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1530-L1592

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.erasureCorrection_cost_outside_counique_lt
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (S : Finset (Fin (3 * r))) (a : Fin (3 * r))
    (ha : a ∈ c0Shadow u)
    (hCounique :
      4 * RandomBase.checkDegree baseSample a <
        5 * RandomBase.couniqueDegree baseSample S a) :
    let C :=
      (RandomBase.couniqueNeighbors baseSample S).filter
        fun b => baseSample (a, b)
    (∑ b ∈ (Finset.univ \ C),
        HammingWeight
          (horizontalFiber
            (bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (eraseC0FiberCorrection u a)) b)) <
      C.card * HammingWeight (c0Fiber u a) := by sorry
