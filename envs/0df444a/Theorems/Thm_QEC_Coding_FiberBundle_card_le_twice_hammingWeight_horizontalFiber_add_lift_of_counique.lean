-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_le_twice_hammingWeight_horizontalFiber_add_lift_of_counique
-- name    : QEC.Coding.FiberBundle.card_le_twice_hammingWeight_horizontalFiber_add_lift_of_counique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:56:39.905134+00:00
-- url     : https://prove2.me/theorems/70aa555b-510f-4488-9fd8-6287daec3f88
-- title:
--   Fiber Bundle: card le twice hamming Weight horizontal Fiber add lift of counique
-- statement:
--   If the counique variable also belongs to the support of the lifted base
--   one-cochain, adding that lift complements the normalized coboundary fiber.
--   Consequently the resulting horizontal fiber occupies at least half the fiber.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1054-L1101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1054-L1101

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.card_le_twice_hammingWeight_horizontalFiber_add_lift_of_counique
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
        (horizontalFiber
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (normalizeC0Fibers u)) b) := by sorry
