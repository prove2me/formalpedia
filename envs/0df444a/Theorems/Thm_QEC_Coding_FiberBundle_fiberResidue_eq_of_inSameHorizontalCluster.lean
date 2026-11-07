-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_fiberResidue_eq_of_inSameHorizontalCluster
-- name    : QEC.Coding.FiberBundle.fiberResidue_eq_of_inSameHorizontalCluster
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:50:24.083944+00:00
-- url     : https://prove2.me/theorems/2a4f7003-97f4-4d9a-a207-9edf940420e5
-- title:
--   Fiber Bundle: fiber Residue eq of in Same Horizontal Cluster
-- statement:
--   Every horizontal overlap cluster has one well-defined fiber residue.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1062-L1075
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1062-L1075

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.fiberResidue_eq_of_inSameHorizontalCluster
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    {x y : Fin (4 * r) × ZMod (ell * ell)}
    (hxy : InSameHorizontalCluster baseSample twistSample x y) :
    fiberResidue ell x.2 = fiberResidue ell y.2 := by sorry
