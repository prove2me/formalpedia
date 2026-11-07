-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_fiberResidue_clusterSubchain_eq_root
-- name    : QEC.Coding.FiberBundle.fiberResidue_clusterSubchain_eq_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:50:34.123317+00:00
-- url     : https://prove2.me/theorems/efb25d17-1d41-4236-8789-59c70e112ad1
-- title:
--   Fiber Bundle: fiber Residue cluster Subchain eq root
-- statement:
--   Every nonzero cluster subchain has the residue of its root.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1361-L1376
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1361-L1376

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.fiberResidue_clusterSubchain_eq_root
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
    fiberResidue ell x.2 = fiberResidue ell root.2 := by sorry
