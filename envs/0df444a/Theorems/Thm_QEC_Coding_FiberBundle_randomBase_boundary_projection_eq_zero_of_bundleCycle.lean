-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_randomBase_boundary_projection_eq_zero_of_bundleCycle
-- name    : QEC.Coding.FiberBundle.randomBase_boundary_projection_eq_zero_of_bundleCycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:48:38.339682+00:00
-- url     : https://prove2.me/theorems/acef1a8c-ea6c-4005-8b75-9cd5168c0649
-- title:
--   Fiber Bundle: random Base boundary projection eq zero of bundle Cycle
-- statement:
--   Specialized cycle-projection equation for the sampled HHO20 bundle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L210-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L210-L244

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.randomBase_boundary_projection_eq_zero_of_bundleCycle
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
    (∑ b : Fin (4 * r),
      homologyBaseProjection z b *
        RandomBase.boundary baseSample a b) = 0 := by sorry
