-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_inSameSupportedHorizontalCluster_tail
-- name    : QEC.Coding.FiberBundle.inSameSupportedHorizontalCluster_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:50:40.178304+00:00
-- url     : https://prove2.me/theorems/f641183f-1883-4a7c-a270-6d05d64e8ba9
-- title:
--   Fiber Bundle: in Same Supported Horizontal Cluster tail
-- statement:
--   A supported horizontal neighbor of a supported cell already reached from the
--   root belongs to the same support-induced cluster.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1341-L1358
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1341-L1358

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.inSameSupportedHorizontalCluster_tail
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root x y : Fin (4 * r) × ZMod (ell * ell))
    (hxCluster : InSameSupportedHorizontalCluster
      baseSample twistSample z root x)
    (hxSupport : z (Sum.inl x) ≠ 0)
    (hySupport : z (Sum.inl y) ≠ 0)
    (hxy : HorizontalBoundaryOverlap baseSample twistSample x y) :
    InSameSupportedHorizontalCluster
      baseSample twistSample z root y := by sorry
