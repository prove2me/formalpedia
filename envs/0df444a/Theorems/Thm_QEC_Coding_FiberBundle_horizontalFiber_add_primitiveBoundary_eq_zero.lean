-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontalFiber_add_primitiveBoundary_eq_zero
-- name    : QEC.Coding.FiberBundle.horizontalFiber_add_primitiveBoundary_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:48:48.012217+00:00
-- url     : https://prove2.me/theorems/19ca5184-494b-4d10-b656-91f2bf97bea3
-- title:
--   Fiber Bundle: horizontal Fiber add primitive Boundary eq zero
-- statement:
--   Adding the explicit primitive boundary clears the full horizontal sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L395-L428
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L395-L428

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontalFiber_add_primitiveBoundary_eq_zero
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
        (z +
          boundary2
            (RandomTwist.fiberBundleData baseSample twistSample)
            (horizontalFiberPrimitiveTwoChain z)) b = 0 := by sorry
