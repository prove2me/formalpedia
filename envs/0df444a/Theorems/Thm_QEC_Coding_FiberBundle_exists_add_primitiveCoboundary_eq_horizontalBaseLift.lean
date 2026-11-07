-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_exists_add_primitiveCoboundary_eq_horizontalBaseLift
-- name    : QEC.Coding.FiberBundle.exists_add_primitiveCoboundary_eq_horizontalBaseLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:07:39.137197+00:00
-- url     : https://prove2.me/theorems/8e8662f3-8c81-4eff-bb9c-e0255501937e
-- title:
--   Fiber Bundle: exists add primitive Coboundary eq horizontal Base Lift
-- statement:
--   After clearing its vertical fibers, a bundle cocycle is exactly the
--   all-one-fiber lift of one base one-cochain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L429-L500
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L429-L500

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.exists_add_primitiveCoboundary_eq_horizontalBaseLift
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
    ∃ x : Word (ZMod 2) (Fin (4 * r)),
      z +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (verticalFiberPrimitiveWord z) =
        horizontalBaseLift
          (baseZero := Fin (3 * r))
          (fiberZero := ZMod (ell * ell))
          (fiberOne := ZMod (ell * ell)) x := by sorry
