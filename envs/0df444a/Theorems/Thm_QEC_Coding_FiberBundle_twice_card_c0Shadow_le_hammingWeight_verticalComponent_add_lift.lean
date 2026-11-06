-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_twice_card_c0Shadow_le_hammingWeight_verticalComponent_add_lift
-- name    : QEC.Coding.FiberBundle.twice_card_c0Shadow_le_hammingWeight_verticalComponent_add_lift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:57:33.249296+00:00
-- url     : https://prove2.me/theorems/ac1090e0-f3dc-4b37-9258-bf5d2f50ec74
-- title:
--   Fiber Bundle: twice card c0 Shadow le hamming Weight vertical Component add lift
-- statement:
--   The same large-shadow lower bound holds for the full normalized representative,
--   because the lifted base cochain has no vertical coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2099-L2120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2099-L2120

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.twice_card_c0Shadow_le_hammingWeight_verticalComponent_add_lift
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell)))) :
    2 * (c0Shadow (normalizeC0Fibers u)).card ≤
      HammingWeight
        (verticalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (normalizeC0Fibers u))) := by sorry
