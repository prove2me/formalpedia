-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_oneStepSlide_mem_middleCycleCode
-- name    : QEC.Coding.FiberBundle.oneStepSlide_mem_middleCycleCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:53:44.18919+00:00
-- url     : https://prove2.me/theorems/906200c8-7986-461f-ae40-da041b8cf53d
-- title:
--   Fiber Bundle: one Step Slide mem middle Cycle Code
-- statement:
--   Sliding a bundle cycle produces another bundle cycle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3618-L3648
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3618-L3648

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.oneStepSlide_mem_middleCycleCode
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier) :
    oneStepSlide baseSample twistSample z h ∈
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier := by sorry
