-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_le_twice_hammingWeight_horizontalComponent_add_lift_of_counique_of_normalized
-- name    : QEC.Coding.FiberBundle.card_le_twice_hammingWeight_horizontalComponent_add_lift_of_counique_of_normalized
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:57:02.861849+00:00
-- url     : https://prove2.me/theorems/cec38498-d3ed-48ae-9e99-1dbf46520e93
-- title:
--   Fiber Bundle: card le twice hamming Weight horizontal Component add lift of counique of normalized
-- statement:
--   The generic counique-support case forces the whole horizontal sector to
--   occupy at least half a fiber.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1705-L1743
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1705-L1743

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.card_le_twice_hammingWeight_horizontalComponent_add_lift_of_counique_of_normalized
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hu : C0FibersNormalized u)
    (b : Fin (4 * r))
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample (c0Shadow u))
    (hxb : x b ≠ 0) :
    Fintype.card (ZMod (ell * ell)) ≤
      2 * HammingWeight
        (horizontalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u)) := by sorry
