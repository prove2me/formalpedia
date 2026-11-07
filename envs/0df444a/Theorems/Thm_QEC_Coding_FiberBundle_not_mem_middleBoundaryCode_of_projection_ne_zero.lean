-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_not_mem_middleBoundaryCode_of_projection_ne_zero
-- name    : QEC.Coding.FiberBundle.not_mem_middleBoundaryCode_of_projection_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:48:41.625392+00:00
-- url     : https://prove2.me/theorems/1cb7955a-ee9e-42de-8847-8922f271b110
-- title:
--   Fiber Bundle: not mem middle Boundary Code of projection ne zero
-- statement:
--   A bundle one-boundary has zero base projection.  Consequently, a nonzero
--   projection is an explicit certificate that a bundle cycle is homologically
--   nontrivial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L251-L269
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L251-L269

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.not_mem_middleBoundaryCode_of_projection_ne_zero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hzProjection : homologyBaseProjection z ≠ 0) :
    z ∉ (chainComplex
      (RandomTwist.fiberBundleData baseSample twistSample)
      ).middleBoundaryCode.carrier := by sorry
