-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_exists_nontrivial_horizontalBaseLift_add_bundleCoboundary_eq
-- name    : QEC.Coding.FiberBundle.exists_nontrivial_horizontalBaseLift_add_bundleCoboundary_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:08:09.005511+00:00
-- url     : https://prove2.me/theorems/6c9b8110-7700-4591-a778-80844f7c1e3d
-- title:
--   Fiber Bundle: exists nontrivial horizontal Base Lift add bundle Coboundary eq
-- statement:
--   Complete source-form representative theorem: every nontrivial bundle
--   cohomology representative over a full-row-rank base is a lifted nontrivial
--   base cohomology representative plus a bundle coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L657-L689
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L657-L689

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.exists_nontrivial_horizontalBaseLift_add_bundleCoboundary_eq
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
    (hzNontrivial :
      z ∉ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).firstCoboundaryCheckCode.carrier) :
    ∃ x : Word (ZMod 2) (Fin (4 * r)),
      IsNontrivialBaseCohomology baseSample x ∧
      ∃ u : Word (ZMod 2)
        (C0Index (Fin (3 * r)) (ZMod (ell * ell))),
        z =
          horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u := by sorry
