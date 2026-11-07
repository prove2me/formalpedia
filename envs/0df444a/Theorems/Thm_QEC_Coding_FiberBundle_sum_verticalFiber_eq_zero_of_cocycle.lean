-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_sum_verticalFiber_eq_zero_of_cocycle
-- name    : QEC.Coding.FiberBundle.sum_verticalFiber_eq_zero_of_cocycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:07:12.999468+00:00
-- url     : https://prove2.me/theorems/896406b0-6c7c-41e5-8bb4-eaa7f292515d
-- title:
--   Fiber Bundle: sum vertical Fiber eq zero of cocycle
-- statement:
--   Full row rank forces every vertical fiber of a bundle cocycle to have even parity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L288-L339
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L288-L339

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.sum_verticalFiber_eq_zero_of_cocycle
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
    (∑ j : ZMod (ell * ell), verticalFiber z a j) = 0 := by sorry
