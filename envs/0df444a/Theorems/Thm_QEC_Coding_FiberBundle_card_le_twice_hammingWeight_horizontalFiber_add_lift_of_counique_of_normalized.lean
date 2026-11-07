-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_le_twice_hammingWeight_horizontalFiber_add_lift_of_counique_of_normalized
-- name    : QEC.Coding.FiberBundle.card_le_twice_hammingWeight_horizontalFiber_add_lift_of_counique_of_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:56:17.159106+00:00
-- url     : https://prove2.me/theorems/1fd82b34-bd38-4cfa-9e02-5c88efff4e44
-- title:
--   Fiber Bundle: card le twice hamming Weight horizontal Fiber add lift of counique of normalized
-- statement:
--   If a counique variable is in the lifted base support, adding the lift
--   complements the light coboundary fiber.  This generic form is stable under
--   any number of shadow erasures.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1003-L1047
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1003-L1047

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.card_le_twice_hammingWeight_horizontalFiber_add_lift_of_counique_of_normalized
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
        (horizontalFiber
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u) b) := by sorry
