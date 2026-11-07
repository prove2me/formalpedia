-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_oneStepSlide_horizontalComponent
-- name    : QEC.Coding.FiberBundle.hammingWeight_oneStepSlide_horizontalComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:12:09.259689+00:00
-- url     : https://prove2.me/theorems/07050cb6-23d8-4afc-8d6a-599955695345
-- title:
--   Fiber Bundle: hamming Weight one Step Slide horizontal Component
-- statement:
--   A global one-step slide of a cycle preserves its weight exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4636-L4654
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4636-L4654

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_oneStepSlide_horizontalComponent
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
    HammingWeight
        (oneStepSlide baseSample twistSample z
          (horizontalComponent z)) =
      HammingWeight z := by sorry
