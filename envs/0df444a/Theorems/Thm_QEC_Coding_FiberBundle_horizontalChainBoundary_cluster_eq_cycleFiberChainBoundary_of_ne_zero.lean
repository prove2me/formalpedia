-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontalChainBoundary_cluster_eq_cycleFiberChainBoundary_of_ne_zero
-- name    : QEC.Coding.FiberBundle.horizontalChainBoundary_cluster_eq_cycleFiberChainBoundary_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:53:07.603271+00:00
-- url     : https://prove2.me/theorems/55064dc6-288d-4486-8d18-40098691206b
-- title:
--   Fiber Bundle: horizontal Chain Boundary cluster eq cycle Fiber Chain Boundary of ne zero
-- statement:
--   Thus every nonzero boundary coordinate of a support-induced cluster is a
--   genuine boundary coordinate of the vertical cycle fiber.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3181-L3207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3181-L3207

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontalChainBoundary_cluster_eq_cycleFiberChainBoundary_of_ne_zero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (root : Fin (4 * r) × ZMod (ell * ell))
    (a : Fin (3 * r)) (j : ZMod (ell * ell))
    (hg :
      horizontalChainBoundary baseSample twistSample
        (horizontalClusterSubchain
          baseSample twistSample z root) a j ≠ 0) :
    horizontalChainBoundary baseSample twistSample
        (horizontalClusterSubchain
          baseSample twistSample z root) a j =
      cycleFiberChainBoundary (ell * ell) (verticalFiber z a) j := by sorry
