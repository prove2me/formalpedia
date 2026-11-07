-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_verticalComponent_eraseC0Fiber_le
-- name    : QEC.Coding.FiberBundle.hammingWeight_verticalComponent_eraseC0Fiber_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:57:14.21106+00:00
-- url     : https://prove2.me/theorems/05121cf0-e109-4cea-91cc-cd9dbeb81c8e
-- title:
--   Fiber Bundle: hamming Weight vertical Component erase C0 Fiber le
-- statement:
--   Erasing one degree-zero fiber cannot increase total vertical weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1918-L1950
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1918-L1950

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_verticalComponent_eraseC0Fiber_le
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a : Fin (3 * r)) :
    HammingWeight
        (verticalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (eraseC0Fiber u a))) ≤
      HammingWeight
        (verticalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u)) := by sorry
