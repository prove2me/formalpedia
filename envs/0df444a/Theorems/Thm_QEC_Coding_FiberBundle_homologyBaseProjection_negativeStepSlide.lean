-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_negativeStepSlide
-- name    : QEC.Coding.FiberBundle.homologyBaseProjection_negativeStepSlide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:10:48.259893+00:00
-- url     : https://prove2.me/theorems/2a94e39f-d2f7-48d1-96bd-46045546a83e
-- title:
--   Fiber Bundle: homology Base Projection negative Step Slide
-- statement:
--   A negative slide leaves the bundle-to-base homology projection unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3780-L3795
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3780-L3795

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.homologyBaseProjection_negativeStepSlide
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    homologyBaseProjection
        (negativeStepSlide baseSample twistSample z h) =
      homologyBaseProjection z := by sorry
