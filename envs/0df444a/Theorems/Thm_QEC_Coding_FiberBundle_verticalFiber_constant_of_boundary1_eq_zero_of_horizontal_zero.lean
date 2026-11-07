-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_verticalFiber_constant_of_boundary1_eq_zero_of_horizontal_zero
-- name    : QEC.Coding.FiberBundle.verticalFiber_constant_of_boundary1_eq_zero_of_horizontal_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:49:23.192071+00:00
-- url     : https://prove2.me/theorems/fdb41a6b-bb13-41b9-9d40-01001f672478
-- title:
--   Fiber Bundle: vertical Fiber constant of boundary1 eq zero of horizontal zero
-- statement:
--   Once all horizontal fibers vanish, the bundle cycle equation says that every
--   remaining vertical fiber is a constant multiple of the fiber fundamental
--   cycle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L452-L491
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L452-L491

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.verticalFiber_constant_of_boundary1_eq_zero_of_horizontal_zero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hzCycle :
      boundary1
        (RandomTwist.fiberBundleData baseSample twistSample) z = 0)
    (hzHorizontal : ∀ b : Fin (4 * r), horizontalFiber z b = 0)
    (a : Fin (3 * r)) :
    ∀ j, verticalFiber z a j = verticalFiber z a 0 := by sorry
