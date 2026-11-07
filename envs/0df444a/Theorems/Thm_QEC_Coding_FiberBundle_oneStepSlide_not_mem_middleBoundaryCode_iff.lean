-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_oneStepSlide_not_mem_middleBoundaryCode_iff
-- name    : QEC.Coding.FiberBundle.oneStepSlide_not_mem_middleBoundaryCode_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:10:27.068245+00:00
-- url     : https://prove2.me/theorems/9fe5213f-131a-4cbd-9ffa-34bb3bde6be3
-- title:
--   Fiber Bundle: one Step Slide not mem middle Boundary Code iff
-- statement:
--   Consequently, one sliding step preserves homological nontriviality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3724-L3744
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3724-L3744

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.oneStepSlide_not_mem_middleBoundaryCode_iff
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    oneStepSlide baseSample twistSample z h ∉
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ↔
      z ∉
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier := by sorry
