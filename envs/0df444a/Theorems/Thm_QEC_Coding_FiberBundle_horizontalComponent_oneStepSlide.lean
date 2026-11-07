-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontalComponent_oneStepSlide
-- name    : QEC.Coding.FiberBundle.horizontalComponent_oneStepSlide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:47:31.818082+00:00
-- url     : https://prove2.me/theorems/bc60fe32-1588-4691-80dd-6dd8d0061f87
-- title:
--   Fiber Bundle: horizontal Component one Step Slide
-- statement:
--   Horizontal sector after a slide: delete the subchain and add its shift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1733-L1766
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1733-L1766

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontalComponent_oneStepSlide
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
        (oneStepSlide baseSample twistSample z h) =
      (horizontalComponent z + h) +
        shiftHorizontalSubchain (ell * ell) h := by sorry
