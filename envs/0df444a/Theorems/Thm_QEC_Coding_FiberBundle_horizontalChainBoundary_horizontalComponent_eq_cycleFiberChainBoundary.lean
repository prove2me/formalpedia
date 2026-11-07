-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontalChainBoundary_horizontalComponent_eq_cycleFiberChainBoundary
-- name    : QEC.Coding.FiberBundle.horizontalChainBoundary_horizontalComponent_eq_cycleFiberChainBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:44:50.687711+00:00
-- url     : https://prove2.me/theorems/4fc450cf-57c7-47cf-9e86-fb58fe86c8f2
-- title:
--   Fiber Bundle: horizontal Chain Boundary horizontal Component eq cycle Fiber Chain Boundary
-- statement:
--   For a bundle cycle, the full horizontal boundary contribution at a base
--   zero-cell is exactly the cycle boundary of the vertical fiber there.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2785-L2815
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2785-L2815

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontalChainBoundary_horizontalComponent_eq_cycleFiberChainBoundary
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (a : Fin (3 * r)) :
    horizontalChainBoundary baseSample twistSample
        (horizontalComponent z) a =
      cycleFiberChainBoundary (ell * ell) (verticalFiber z a) := by sorry
