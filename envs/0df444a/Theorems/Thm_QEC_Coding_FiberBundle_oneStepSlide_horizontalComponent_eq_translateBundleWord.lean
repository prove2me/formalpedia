-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_oneStepSlide_horizontalComponent_eq_translateBundleWord
-- name    : QEC.Coding.FiberBundle.oneStepSlide_horizontalComponent_eq_translateBundleWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:47:49.051193+00:00
-- url     : https://prove2.me/theorems/2f8cc842-9785-44d1-a0be-2ffcc6de1297
-- title:
--   Fiber Bundle: one Step Slide horizontal Component eq translate Bundle Word
-- statement:
--   Sliding the complete horizontal sector of a bundle cycle once is exactly
--   global translation by one fiber cell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4515-L4633
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4515-L4633

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.oneStepSlide_horizontalComponent_eq_translateBundleWord
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
    oneStepSlide baseSample twistSample z (horizontalComponent z) =
      translateBundleWord (ell * ell) 1 z := by sorry
