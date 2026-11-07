-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_verticalFiber_negativeStepSlide
-- name    : QEC.Coding.FiberBundle.verticalFiber_negativeStepSlide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:53:09.255536+00:00
-- url     : https://prove2.me/theorems/9ebd9dae-cdd3-4667-a410-36f4cae713e8
-- title:
--   Fiber Bundle: vertical Fiber negative Step Slide
-- statement:
--   The vertical sector of a negative slide is the backward toggle of the same
--   horizontal boundary word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3248-L3290
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3248-L3290

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.verticalFiber_negativeStepSlide
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (a : Fin (3 * r)) :
    verticalFiber
        (negativeStepSlide baseSample twistSample z h) a =
      verticalFiber z a +
        backwardVertexToggle (ell * ell)
          (horizontalChainBoundary baseSample twistSample h a) := by sorry
