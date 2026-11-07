-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_baseDistance_bound_of_nontrivial_bundleCycle
-- name    : QEC.Coding.FiberBundle.baseDistance_bound_of_nontrivial_bundleCycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:46:39.266328+00:00
-- url     : https://prove2.me/theorems/7d59529e-e02e-4f76-a0d2-d365b9d53bbd
-- title:
--   Fiber Bundle: base Distance bound of nontrivial bundle Cycle
-- statement:
--   The sampled base-distance event forces at least `4r/5` distinct projected
--   base variables in every nontrivial bundle homology representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L834-L858
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L834-L858

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.baseDistance_bound_of_nontrivial_bundleCycle
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (hDistance : RandomBase.HasLinearDistance baseSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (hzNontrivial :
      z ∉ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleBoundaryCode.carrier) :
    4 * r ≤ 5 * HammingWeight (homologyBaseProjection z) := by sorry
