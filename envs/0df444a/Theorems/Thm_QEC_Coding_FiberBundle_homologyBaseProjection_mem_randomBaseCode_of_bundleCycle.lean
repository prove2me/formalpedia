-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_mem_randomBaseCode_of_bundleCycle
-- name    : QEC.Coding.FiberBundle.homologyBaseProjection_mem_randomBaseCode_of_bundleCycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:49:39.694457+00:00
-- url     : https://prove2.me/theorems/b15765df-da19-466e-a1b7-d45e52152fea
-- title:
--   Fiber Bundle: homology Base Projection mem random Base Code of bundle Cycle
-- statement:
--   The projection of a bundle cycle belongs to the sampled classical code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L770-L792
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L770-L792

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.homologyBaseProjection_mem_randomBaseCode_of_bundleCycle
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
        ).middleCycleCode.carrier) :
    homologyBaseProjection z ∈
      (RandomBase.code baseSample).carrier := by sorry
