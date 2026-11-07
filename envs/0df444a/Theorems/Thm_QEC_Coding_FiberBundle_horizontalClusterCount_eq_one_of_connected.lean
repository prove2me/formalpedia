-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontalClusterCount_eq_one_of_connected
-- name    : QEC.Coding.FiberBundle.horizontalClusterCount_eq_one_of_connected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:55:38.520211+00:00
-- url     : https://prove2.me/theorems/ade8f701-080d-4d95-8074-3f1a0df65d64
-- title:
--   Fiber Bundle: horizontal Cluster Count eq one of connected
-- statement:
--   A nonempty connected support has exactly one horizontal cluster.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1202-L1226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1202-L1226

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontalClusterCount_eq_one_of_connected
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root : SupportedHorizontalCell z)
    (hConnected :
      ∀ x : SupportedHorizontalCell z,
        InSameSupportedHorizontalCluster
          baseSample twistSample z root.1 x.1) :
    horizontalClusterCount baseSample twistSample z = 1 := by sorry
