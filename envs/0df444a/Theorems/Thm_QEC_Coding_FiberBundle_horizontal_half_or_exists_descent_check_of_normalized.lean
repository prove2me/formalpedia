-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontal_half_or_exists_descent_check_of_normalized
-- name    : QEC.Coding.FiberBundle.horizontal_half_or_exists_descent_check_of_normalized
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:54:21.676322+00:00
-- url     : https://prove2.me/theorems/ea2b456d-9ba6-40ae-91bd-46db841af4e6
-- title:
--   Fiber Bundle: horizontal half or exists descent check of normalized
-- statement:
--   For a nonempty small shadow of any fiberwise-normalized representative,
--   either a supported counique variable forces half-fiber horizontal weight or
--   the selected `> 4/5` counique check is disjoint from the lifted base support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2480-L2522
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2480-L2522

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontal_half_or_exists_descent_check_of_normalized
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hu : C0FibersNormalized u)
    (hDelta : 0 < Delta)
    (hDegree : RandomBase.HasDegreeWindows (Delta := Delta) baseSample)
    (hExpansion :
      RandomBase.HasStrongSmallSetExpansion (Delta := Delta) baseSample)
    (hShadowNonempty : (c0Shadow u).Nonempty)
    (hSmall : 100000 * Delta * (c0Shadow u).card ≤ 3 * r) :
    Fintype.card (ZMod (ell * ell)) ≤
        2 * HammingWeight
          (horizontalComponent
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample) u)) ∨
      ∃ a ∈ c0Shadow u,
        4 * RandomBase.checkDegree baseSample a <
          5 * RandomBase.couniqueDegree baseSample (c0Shadow u) a ∧
        ∀ b ∈ RandomBase.couniqueNeighbors baseSample (c0Shadow u),
          x b = 0 := by sorry
