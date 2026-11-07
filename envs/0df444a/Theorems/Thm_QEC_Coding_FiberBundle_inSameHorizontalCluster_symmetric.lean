-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_inSameHorizontalCluster_symmetric
-- name    : QEC.Coding.FiberBundle.inSameHorizontalCluster_symmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:55:22.378025+00:00
-- url     : https://prove2.me/theorems/6c7ddb6d-a307-474f-9423-9014bc5c94d0
-- title:
--   Fiber Bundle: in Same Horizontal Cluster symmetric
-- statement:
--   Cluster connectivity is symmetric because boundary overlap is symmetric.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1078-L1086
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1078-L1086

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.inSameHorizontalCluster_symmetric
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    Symmetric (InSameHorizontalCluster baseSample twistSample) := by sorry
