-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontal_half_or_exists_descent_check
-- name    : QEC.Coding.FiberBundle.horizontal_half_or_exists_descent_check
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:33:31.810724+00:00
-- url     : https://prove2.me/theorems/5e568115-06af-45da-a21f-90a9cf0931e6
-- title:
--   Fiber Bundle: horizontal half or exists descent check
-- statement:
--   For a nonempty small normalized shadow, either a supported counique variable
--   already forces half-fiber horizontal weight, or the selected `> 4/5`
--   counique check is disjoint from the lifted base support.  The latter is the
--   strict-descent branch of HHO20's proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2763-L2810
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2763-L2810

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontal_half_or_exists_descent_check
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hDelta : 0 < Delta)
    (hDegree : RandomBase.HasDegreeWindows (Delta := Delta) baseSample)
    (hExpansion :
      RandomBase.HasStrongSmallSetExpansion (Delta := Delta) baseSample)
    (hShadowNonempty : (c0Shadow (normalizeC0Fibers u)).Nonempty)
    (hSmall :
      100000 * Delta * (c0Shadow (normalizeC0Fibers u)).card ≤ 3 * r) :
    Fintype.card (ZMod (ell * ell)) ≤
        2 * HammingWeight
          (horizontalComponent
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample)
                (normalizeC0Fibers u))) ∨
      ∃ a ∈ c0Shadow (normalizeC0Fibers u),
        4 * RandomBase.checkDegree baseSample a <
          5 * RandomBase.couniqueDegree baseSample
            (c0Shadow (normalizeC0Fibers u)) a ∧
        ∀ b ∈ RandomBase.couniqueNeighbors baseSample
            (c0Shadow (normalizeC0Fibers u)),
          x b = 0 := by sorry
