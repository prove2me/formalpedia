-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalComponent_bundleCoboundary_eraseC0FiberCorrection
-- name    : QEC.Coding.FiberBundle.hammingWeight_horizontalComponent_bundleCoboundary_eraseC0FiberCorrection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:56:37.650542+00:00
-- url     : https://prove2.me/theorems/1330473f-c46d-44d7-8c23-788b80373052
-- title:
--   Fiber Bundle: hamming Weight horizontal Component bundle Coboundary erase C0 Fiber Correction
-- statement:
--   The total horizontal cost of erasing one fiber is degree times fiber weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1420-L1440
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1420-L1440

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_horizontalComponent_bundleCoboundary_eraseC0FiberCorrection
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a : Fin (3 * r)) :
    HammingWeight
        (horizontalComponent
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (eraseC0FiberCorrection u a))) =
      RandomBase.checkDegree baseSample a * HammingWeight (c0Fiber u a) := by sorry
