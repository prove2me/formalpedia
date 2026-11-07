-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontalComponent_negativeStepSlide
-- name    : QEC.Coding.FiberBundle.horizontalComponent_negativeStepSlide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:52:09.008045+00:00
-- url     : https://prove2.me/theorems/38104fa9-f24e-49cf-bd0b-078ca499c7b6
-- title:
--   Fiber Bundle: horizontal Component negative Step Slide
-- statement:
--   Horizontal sector after a negative slide: delete the subchain and shift it backward.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1975-L2008
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1975-L2008

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontalComponent_negativeStepSlide
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    horizontalComponent
        (negativeStepSlide baseSample twistSample z h) =
      (horizontalComponent z + h) +
        backwardShiftHorizontalSubchain (ell * ell) h := by sorry
