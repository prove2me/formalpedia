-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontalFiber_boundary2_negativeStepSlideTwoChain
-- name    : QEC.Coding.FiberBundle.horizontalFiber_boundary2_negativeStepSlideTwoChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:51:50.783938+00:00
-- url     : https://prove2.me/theorems/b9dd2381-85f4-4c79-a070-0c0a95d29e99
-- title:
--   Fiber Bundle: horizontal Fiber boundary2 negative Step Slide Two Chain
-- statement:
--   Exact horizontal coordinate formula for a negative sliding boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1950-L1972
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1950-L1972

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontalFiber_boundary2_negativeStepSlideTwoChain
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (b : Fin (4 * r)) (i : ZMod (ell * ell)) :
    horizontalFiber
        (boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (negativeStepSlideTwoChain (ell * ell) h)) b i =
      h (b, i + 1) + h (b, i) := by sorry
