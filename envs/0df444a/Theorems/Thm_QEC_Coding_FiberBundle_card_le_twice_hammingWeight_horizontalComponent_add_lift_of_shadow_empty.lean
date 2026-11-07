-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_le_twice_hammingWeight_horizontalComponent_add_lift_of_shadow_empty
-- name    : QEC.Coding.FiberBundle.card_le_twice_hammingWeight_horizontalComponent_add_lift_of_shadow_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:54:22.157439+00:00
-- url     : https://prove2.me/theorems/a226f0f9-fe81-411f-a61a-9805935b36ad
-- title:
--   Fiber Bundle: card le twice hamming Weight horizontal Component add lift of shadow empty
-- statement:
--   When the zero-cell shadow is empty, a nonzero lifted base cochain contributes
--   an entire horizontal fiber.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1749-L1811
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1749-L1811

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.card_le_twice_hammingWeight_horizontalComponent_add_lift_of_shadow_empty
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hx : x ≠ 0)
    (hShadow : c0Shadow u = ∅) :
    Fintype.card (ZMod (ell * ell)) ≤
      2 * HammingWeight
        (horizontalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u)) := by sorry
