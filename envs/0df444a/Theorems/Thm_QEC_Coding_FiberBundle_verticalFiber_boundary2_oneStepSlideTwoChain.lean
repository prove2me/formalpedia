-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_verticalFiber_boundary2_oneStepSlideTwoChain
-- name    : QEC.Coding.FiberBundle.verticalFiber_boundary2_oneStepSlideTwoChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:47:20.50847+00:00
-- url     : https://prove2.me/theorems/f494a32a-0b69-4521-8a6a-07b131b5a224
-- title:
--   Fiber Bundle: vertical Fiber boundary2 one Step Slide Two Chain
-- statement:
--   Exact vertical coordinate formula for one discrete sliding boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1672-L1693
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1672-L1693

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.verticalFiber_boundary2_oneStepSlideTwoChain
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (a : Fin (3 * r)) (j : ZMod (ell * ell)) :
    verticalFiber
        (boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (oneStepSlideTwoChain h)) a j =
      ∑ b : Fin (4 * r),
        RandomBase.boundary baseSample a b *
          h (b,
            (((RandomTwist.fiberBundleData baseSample twistSample
              ).connection b a).onOne.symm) j) := by sorry
