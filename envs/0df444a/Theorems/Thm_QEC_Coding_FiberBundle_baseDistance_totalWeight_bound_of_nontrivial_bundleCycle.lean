-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_baseDistance_totalWeight_bound_of_nontrivial_bundleCycle
-- name    : QEC.Coding.FiberBundle.baseDistance_totalWeight_bound_of_nontrivial_bundleCycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:55:19.979071+00:00
-- url     : https://prove2.me/theorems/28d7ad2e-08f9-4824-a3c3-d8fb64cafe20
-- title:
--   Fiber Bundle: base Distance total Weight bound of nontrivial bundle Cycle
-- statement:
--   Coarse total-weight consequence of the base-distance event.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L861-L885
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L861-L885

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.baseDistance_totalWeight_bound_of_nontrivial_bundleCycle
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
    4 * r ≤ 5 * HammingWeight z := by sorry
