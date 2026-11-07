-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_twice_card_c0Shadow_le_hammingWeight_verticalComponent_normalizedCoboundary
-- name    : QEC.Coding.FiberBundle.twice_card_c0Shadow_le_hammingWeight_verticalComponent_normalizedCoboundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:57:29.50742+00:00
-- url     : https://prove2.me/theorems/2561e475-2258-4f3e-8011-e64712674351
-- title:
--   Fiber Bundle: twice card c0 Shadow le hamming Weight vertical Component normalized Coboundary
-- statement:
--   The normalized shadow gives a doubled lower bound on total vertical weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2031-L2066
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2031-L2066

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.twice_card_c0Shadow_le_hammingWeight_verticalComponent_normalizedCoboundary
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell)))) :
    2 * (c0Shadow (normalizeC0Fibers u)).card ≤
      HammingWeight
        (verticalComponent
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (normalizeC0Fibers u))) := by sorry
