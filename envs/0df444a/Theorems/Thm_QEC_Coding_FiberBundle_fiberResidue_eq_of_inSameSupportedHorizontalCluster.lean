-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_fiberResidue_eq_of_inSameSupportedHorizontalCluster
-- name    : QEC.Coding.FiberBundle.fiberResidue_eq_of_inSameSupportedHorizontalCluster
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:46:34.129891+00:00
-- url     : https://prove2.me/theorems/44ffcf9f-394b-4691-a94c-f57437e03e94
-- title:
--   Fiber Bundle: fiber Residue eq of in Same Supported Horizontal Cluster
-- statement:
--   A support-induced cluster still has one fiber residue class.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1282-L1299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1282-L1299

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.fiberResidue_eq_of_inSameSupportedHorizontalCluster
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    {x y : Fin (4 * r) × ZMod (ell * ell)}
    (hxy : InSameSupportedHorizontalCluster
      baseSample twistSample z x y) :
    fiberResidue ell x.2 = fiberResidue ell y.2 := by sorry
