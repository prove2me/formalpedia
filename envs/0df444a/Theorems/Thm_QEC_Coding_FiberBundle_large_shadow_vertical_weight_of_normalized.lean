-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_large_shadow_vertical_weight_of_normalized
-- name    : QEC.Coding.FiberBundle.large_shadow_vertical_weight_of_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:54:16.821955+00:00
-- url     : https://prove2.me/theorems/3d04285b-3f9d-4b21-ba65-f9f929791085
-- title:
--   Fiber Bundle: large shadow vertical weight of normalized
-- statement:
--   The large-shadow lower bound for an arbitrary fiberwise-normalized
--   representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2126-L2149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2126-L2149

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.large_shadow_vertical_weight_of_normalized
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hu : C0FibersNormalized u)
    (hLarge : 3 * r < 100000 * Delta * (c0Shadow u).card) :
    6 * r <
      100000 * Delta *
        HammingWeight
          (verticalComponent
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample) u)) := by sorry
