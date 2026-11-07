-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_oneStepSlide_add_boundary_eq
-- name    : QEC.Coding.FiberBundle.oneStepSlide_add_boundary_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:57:09.647566+00:00
-- url     : https://prove2.me/theorems/1b23d9c0-21da-4e89-af46-8656c787057d
-- title:
--   Fiber Bundle: one Step Slide add boundary eq
-- statement:
--   One sliding step stays in the same middle-homology class.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1715-L1730
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1715-L1730

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.oneStepSlide_add_boundary_eq
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    oneStepSlide baseSample twistSample z h =
      z +
        boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (oneStepSlideTwoChain h) := by sorry
