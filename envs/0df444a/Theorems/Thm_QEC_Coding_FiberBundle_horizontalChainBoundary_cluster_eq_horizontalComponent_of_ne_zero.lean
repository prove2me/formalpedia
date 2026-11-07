-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontalChainBoundary_cluster_eq_horizontalComponent_of_ne_zero
-- name    : QEC.Coding.FiberBundle.horizontalChainBoundary_cluster_eq_horizontalComponent_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:53:08.089018+00:00
-- url     : https://prove2.me/theorems/a00351d2-0a63-4e30-a26d-ff6ccc9c70a0
-- title:
--   Fiber Bundle: horizontal Chain Boundary cluster eq horizontal Component of ne zero
-- statement:
--   If the boundary of a support-induced cluster is nonzero at a coordinate, it
--   equals the boundary of the entire horizontal sector there.  Indeed, one
--   selected contributor at that coordinate overlaps every other supported
--   contributor, so cluster closure selects all of them.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3093-L3175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3093-L3175

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontalChainBoundary_cluster_eq_horizontalComponent_of_ne_zero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root : Fin (4 * r) × ZMod (ell * ell))
    (a : Fin (3 * r)) (j : ZMod (ell * ell))
    (hg :
      horizontalChainBoundary baseSample twistSample
        (horizontalClusterSubchain
          baseSample twistSample z root) a j ≠ 0) :
    horizontalChainBoundary baseSample twistSample
        (horizontalClusterSubchain
          baseSample twistSample z root) a j =
      horizontalChainBoundary baseSample twistSample
        (horizontalComponent z) a j := by sorry
