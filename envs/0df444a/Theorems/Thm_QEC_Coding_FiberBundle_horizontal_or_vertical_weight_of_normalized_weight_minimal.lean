-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontal_or_vertical_weight_of_normalized_weight_minimal
-- name    : QEC.Coding.FiberBundle.horizontal_or_vertical_weight_of_normalized_weight_minimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:57:56.677583+00:00
-- url     : https://prove2.me/theorems/9e643b23-e1c0-4faa-a20a-fa872b69a571
-- title:
--   Fiber Bundle: horizontal or vertical weight of normalized weight minimal
-- statement:
--   For a normalized full-weight-minimal representative with nonzero base
--   cochain, the strict total-weight descent branch is impossible.  Thus the
--   representative obeys either the horizontal half-fiber bound or the vertical
--   large-shadow bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2595-L2652
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2595-L2652

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontal_or_vertical_weight_of_normalized_weight_minimal
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hx : x ≠ 0)
    (hu : C0FibersNormalized u)
    (hMinimal : IsWeightMinimal baseSample twistSample x u)
    (hDelta : 0 < Delta)
    (hDegree : RandomBase.HasDegreeWindows (Delta := Delta) baseSample)
    (hExpansion :
      RandomBase.HasStrongSmallSetExpansion (Delta := Delta) baseSample) :
    Fintype.card (ZMod (ell * ell)) ≤
        2 * HammingWeight
          (horizontalComponent
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample) u)) ∨
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
