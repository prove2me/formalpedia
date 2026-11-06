-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_twice_card_c0Shadow_le_hammingWeight_verticalComponent_coboundary_of_normalized
-- name    : QEC.Coding.FiberBundle.twice_card_c0Shadow_le_hammingWeight_verticalComponent_coboundary_of_normalized
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:57:42.954792+00:00
-- url     : https://prove2.me/theorems/7852a7be-c5ef-41fc-820b-7432c9b77f8f
-- title:
--   Fiber Bundle: twice card c0 Shadow le hamming Weight vertical Component coboundary of normalized
-- statement:
--   A fiberwise-normalized shadow gives a doubled lower bound on vertical weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1998-L2028
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1998-L2028

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.twice_card_c0Shadow_le_hammingWeight_verticalComponent_coboundary_of_normalized
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hu : C0FibersNormalized u) :
    2 * (c0Shadow u).card ≤
      HammingWeight
        (verticalComponent
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u)) := by sorry
