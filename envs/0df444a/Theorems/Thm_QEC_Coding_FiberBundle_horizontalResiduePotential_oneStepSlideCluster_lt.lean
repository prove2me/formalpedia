-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontalResiduePotential_oneStepSlideCluster_lt
-- name    : QEC.Coding.FiberBundle.horizontalResiduePotential_oneStepSlideCluster_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:51:37.026601+00:00
-- url     : https://prove2.me/theorems/0cbd83a8-4467-4b54-a615-5caf04c58851
-- title:
--   Fiber Bundle: horizontal Residue Potential one Step Slide Cluster lt
-- statement:
--   A positive slide of a supported cluster with nonzero residue strictly lowers
--   the residue potential.  Cancellations at the destination can only lower it
--   further.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1824-L1890
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1824-L1890

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontalResiduePotential_oneStepSlideCluster_lt
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root : Fin (4 * r) × ZMod (ell * ell))
    (hRootSupport : z (Sum.inl root) ≠ 0)
    (hRootResidue : fiberResidue ell root.2 ≠ 0) :
    horizontalResiduePotential
        (oneStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) <
      horizontalResiduePotential z := by sorry
