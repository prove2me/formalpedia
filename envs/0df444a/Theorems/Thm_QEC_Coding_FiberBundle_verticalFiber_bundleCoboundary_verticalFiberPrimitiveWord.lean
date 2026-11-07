-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_verticalFiber_bundleCoboundary_verticalFiberPrimitiveWord
-- name    : QEC.Coding.FiberBundle.verticalFiber_bundleCoboundary_verticalFiberPrimitiveWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:07:16.242005+00:00
-- url     : https://prove2.me/theorems/f45a17ce-ce4e-4fc0-959a-73f8a56c5ccf
-- title:
--   Fiber Bundle: vertical Fiber bundle Coboundary vertical Fiber Primitive Word
-- statement:
--   For a cocycle over a full-row-rank base, the coboundary of the explicit
--   vertical primitives reproduces every vertical fiber exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L355-L382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L355-L382

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.verticalFiber_bundleCoboundary_verticalFiberPrimitiveWord
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCocycleCode.carrier)
    (a : Fin (3 * r)) :
    verticalFiber
        (bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample)
          (verticalFiberPrimitiveWord z)) a =
      verticalFiber z a := by sorry
