-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalComponent_oneStepSlide_le
-- name    : QEC.Coding.FiberBundle.hammingWeight_horizontalComponent_oneStepSlide_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:51:36.265563+00:00
-- url     : https://prove2.me/theorems/694bd6f6-b954-4593-b440-d925a8294eaf
-- title:
--   Fiber Bundle: hamming Weight horizontal Component one Step Slide le
-- statement:
--   Sliding any coordinate subword cannot increase horizontal Hamming weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1769-L1797
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1769-L1797

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_horizontalComponent_oneStepSlide_le
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (hhz : IsBinarySubword h (horizontalComponent z)) :
    HammingWeight
        (horizontalComponent
          (oneStepSlide baseSample twistSample z h)) ≤
      HammingWeight (horizontalComponent z) := by sorry
