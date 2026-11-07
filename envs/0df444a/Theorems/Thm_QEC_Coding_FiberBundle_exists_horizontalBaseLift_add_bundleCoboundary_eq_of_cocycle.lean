-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_exists_horizontalBaseLift_add_bundleCoboundary_eq_of_cocycle
-- name    : QEC.Coding.FiberBundle.exists_horizontalBaseLift_add_bundleCoboundary_eq_of_cocycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:07:48.373246+00:00
-- url     : https://prove2.me/theorems/7dec5e3e-516a-4ed2-966d-5156fee55a2f
-- title:
--   Fiber Bundle: exists horizontal Base Lift add bundle Coboundary eq of cocycle
-- statement:
--   Concrete representative form from HHO20 Proposition `prop:cohorep`: every
--   bundle cocycle over a full-row-rank base is a lifted base cochain plus an
--   explicit bundle coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L507-L549
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L507-L549

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.exists_horizontalBaseLift_add_bundleCoboundary_eq_of_cocycle
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
      ∃ u : Word (ZMod 2)
        (C0Index (Fin (3 * r)) (ZMod (ell * ell))),
        z =
          horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u := by sorry
