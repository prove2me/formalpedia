-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontalFiber_boundary2_horizontalFiberPrimitiveTwoChain
-- name    : QEC.Coding.FiberBundle.horizontalFiber_boundary2_horizontalFiberPrimitiveTwoChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:48:47.433819+00:00
-- url     : https://prove2.me/theorems/3a38cdec-4cfd-496e-8c66-cb96fb2dbc28
-- title:
--   Fiber Bundle: horizontal Fiber boundary2 horizontal Fiber Primitive Two Chain
-- statement:
--   When the base projection vanishes, the boundary of the assembled primitives
--   reproduces every horizontal fiber exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L363-L392
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L363-L392

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontalFiber_boundary2_horizontalFiberPrimitiveTwoChain
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hzProjection : homologyBaseProjection z = 0)
    (b : Fin (4 * r)) :
    horizontalFiber
        (boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (horizontalFiberPrimitiveTwoChain z)) b =
      horizontalFiber z b := by sorry
