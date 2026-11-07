-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_connected_of_horizontalClusterCount_eq_one
-- name    : QEC.Coding.FiberBundle.connected_of_horizontalClusterCount_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:50:30.82381+00:00
-- url     : https://prove2.me/theorems/1b3dfb35-7c96-4662-80a7-8e56aac6111b
-- title:
--   Fiber Bundle: connected of horizontal Cluster Count eq one
-- statement:
--   Cluster count one means that every supported cell is connected to any root.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1229-L1256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1229-L1256

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.connected_of_horizontalClusterCount_eq_one
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root : SupportedHorizontalCell z)
    (hCount :
      horizontalClusterCount baseSample twistSample z = 1) :
    ∀ x : SupportedHorizontalCell z,
      InSameSupportedHorizontalCluster
        baseSample twistSample z root.1 x.1 := by sorry
