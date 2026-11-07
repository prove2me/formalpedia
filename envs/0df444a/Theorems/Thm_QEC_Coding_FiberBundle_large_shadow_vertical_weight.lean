-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_large_shadow_vertical_weight
-- name    : QEC.Coding.FiberBundle.large_shadow_vertical_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:31:36.732425+00:00
-- url     : https://prove2.me/theorems/fa9dee93-e81f-4579-bc84-ccf7408ac5d0
-- title:
--   Fiber Bundle: large shadow vertical weight
-- statement:
--   In the paper's large-shadow case, the vertical sector already has the stated
--   inverse-degree scale, with all constants kept as integer inequalities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2155-L2179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2155-L2179

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.large_shadow_vertical_weight
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hLarge :
      3 * r < 100000 * Delta * (c0Shadow (normalizeC0Fibers u)).card) :
    6 * r <
      100000 * Delta *
        HammingWeight
          (verticalComponent
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample)
                (normalizeC0Fibers u))) := by sorry
