-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_le_twice_hammingWeight_horizontalComponent_add_lift_of_counique
-- name    : QEC.Coding.FiberBundle.card_le_twice_hammingWeight_horizontalComponent_add_lift_of_counique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:57:14.5996+00:00
-- url     : https://prove2.me/theorems/f29e6426-5e30-49b0-917a-27a4d90ee64d
-- title:
--   Fiber Bundle: card le twice hamming Weight horizontal Component add lift of counique
-- statement:
--   The preceding counique-support case already forces the whole horizontal
--   sector to occupy at least half a fiber.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1817-L1857
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1817-L1857

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.card_le_twice_hammingWeight_horizontalComponent_add_lift_of_counique
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (b : Fin (4 * r))
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample
      (c0Shadow (normalizeC0Fibers u)))
    (hxb : x b ≠ 0) :
    Fintype.card (ZMod (ell * ell)) ≤
      2 * HammingWeight
        (horizontalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (normalizeC0Fibers u))) := by sorry
