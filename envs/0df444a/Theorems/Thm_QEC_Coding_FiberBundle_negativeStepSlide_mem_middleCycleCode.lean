-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_negativeStepSlide_mem_middleCycleCode
-- name    : QEC.Coding.FiberBundle.negativeStepSlide_mem_middleCycleCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:10:41.860317+00:00
-- url     : https://prove2.me/theorems/29483646-487a-49d9-8bd1-7cef3c3724a1
-- title:
--   Fiber Bundle: negative Step Slide mem middle Cycle Code
-- statement:
--   A negative slide of a bundle cycle also produces a bundle cycle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3747-L3777
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3747-L3777

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.negativeStepSlide_mem_middleCycleCode
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
    negativeStepSlide baseSample twistSample z h ∈
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier := by sorry
