-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_verticalFiber_bundleCoboundary_eraseC0Fiber_le
-- name    : QEC.Coding.FiberBundle.hammingWeight_verticalFiber_bundleCoboundary_eraseC0Fiber_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:57:15.522132+00:00
-- url     : https://prove2.me/theorems/fe47e52a-951e-4c38-bf97-e85dfcef04cb
-- title:
--   Fiber Bundle: hamming Weight vertical Fiber bundle Coboundary erase C0 Fiber le
-- statement:
--   Erasing one degree-zero fiber cannot increase any vertical fiber weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1874-L1915
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1874-L1915

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_verticalFiber_bundleCoboundary_eraseC0Fiber_le
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a a' : Fin (3 * r)) :
    HammingWeight
        (verticalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (eraseC0Fiber u a)) a') ≤
      HammingWeight
        (verticalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u) a') := by sorry
