-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontalFiber_bundleCoboundary_eraseC0FiberCorrection
-- name    : QEC.Coding.FiberBundle.horizontalFiber_bundleCoboundary_eraseC0FiberCorrection
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:53:31.104966+00:00
-- url     : https://prove2.me/theorems/1d0b51b1-fdf4-43e0-877a-6872f1e549e3
-- title:
--   Fiber Bundle: horizontal Fiber bundle Coboundary erase C0 Fiber Correction
-- statement:
--   The horizontal effect of erasing one zero-cell fiber is either zero or one
--   connection-reindexed copy of that fiber, according to the sampled incidence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L743-L771
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L743-L771

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontalFiber_bundleCoboundary_eraseC0FiberCorrection
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a : Fin (3 * r)) (b : Fin (4 * r)) :
    horizontalFiber
        (bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample)
          (eraseC0FiberCorrection u a)) b =
      if baseSample (a, b) then
        reindexWord
          ((RandomTwist.fiberBundleData baseSample twistSample).connection b a).onZero.symm
          (c0Fiber u a)
      else 0 := by sorry
