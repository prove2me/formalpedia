-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_inSameSupportedHorizontalCluster_of_clusterSubchain_ne_zero
-- name    : QEC.Coding.FiberBundle.inSameSupportedHorizontalCluster_of_clusterSubchain_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:46:41.19219+00:00
-- url     : https://prove2.me/theorems/6dddbfa0-1e10-424c-955b-f40033559427
-- title:
--   Fiber Bundle: in Same Supported Horizontal Cluster of cluster Subchain ne zero
-- statement:
--   Every nonzero cell selected by a cluster subchain lies in that cluster.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1320-L1335
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1320-L1335

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.inSameSupportedHorizontalCluster_of_clusterSubchain_ne_zero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root x : Fin (4 * r) × ZMod (ell * ell))
    (hx : horizontalClusterSubchain
      baseSample twistSample z root x ≠ 0) :
    InSameSupportedHorizontalCluster
      baseSample twistSample z root x := by sorry
