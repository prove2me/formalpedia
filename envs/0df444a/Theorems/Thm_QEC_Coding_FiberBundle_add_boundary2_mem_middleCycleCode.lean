-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_add_boundary2_mem_middleCycleCode
-- name    : QEC.Coding.FiberBundle.add_boundary2_mem_middleCycleCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:53:42.642618+00:00
-- url     : https://prove2.me/theorems/e314e211-ebdf-460c-9576-609f7ce756a6
-- title:
--   Fiber Bundle: add boundary2 mem middle Cycle Code
-- statement:
--   Adding an arbitrary degree-two boundary to a cycle preserves the cycle condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3873-L3907
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3873-L3907

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.add_boundary2_mem_middleCycleCode
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (c : Word (ZMod 2)
      (C2Index (Fin (4 * r)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier) :
    z + boundary2
        (RandomTwist.fiberBundleData baseSample twistSample) c ∈
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier := by sorry
