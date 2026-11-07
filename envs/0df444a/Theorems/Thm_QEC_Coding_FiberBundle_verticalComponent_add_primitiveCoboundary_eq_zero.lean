-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_verticalComponent_add_primitiveCoboundary_eq_zero
-- name    : QEC.Coding.FiberBundle.verticalComponent_add_primitiveCoboundary_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:07:31.579234+00:00
-- url     : https://prove2.me/theorems/870745b4-3e92-4f91-b35e-25223508ca87
-- title:
--   Fiber Bundle: vertical Component add primitive Coboundary eq zero
-- statement:
--   Adding the primitive coboundary clears the entire vertical sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L385-L423
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L385-L423

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.verticalComponent_add_primitiveCoboundary_eq_zero
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
        ).middleCocycleCode.carrier) :
    verticalComponent
        (z +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (verticalFiberPrimitiveWord z)) = 0 := by sorry
