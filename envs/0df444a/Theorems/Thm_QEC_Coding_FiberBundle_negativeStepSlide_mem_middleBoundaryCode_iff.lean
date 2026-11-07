-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_negativeStepSlide_mem_middleBoundaryCode_iff
-- name    : QEC.Coding.FiberBundle.negativeStepSlide_mem_middleBoundaryCode_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:53:51.118227+00:00
-- url     : https://prove2.me/theorems/27491046-284e-4be0-bf24-2b9f32c10fca
-- title:
--   Fiber Bundle: negative Step Slide mem middle Boundary Code iff
-- statement:
--   Adding a negative sliding boundary preserves boundary membership.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3798-L3825
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3798-L3825

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.negativeStepSlide_mem_middleBoundaryCode_iff
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    negativeStepSlide baseSample twistSample z h ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ↔
      z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier := by sorry
