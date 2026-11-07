-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_weight_bound_for_all_corrections_of_nontrivial_base
-- name    : QEC.Coding.FiberBundle.weight_bound_for_all_corrections_of_nontrivial_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:05:36.629952+00:00
-- url     : https://prove2.me/theorems/3b414a65-e055-4913-806e-3414a5486191
-- title:
--   Fiber Bundle: weight bound for all corrections of nontrivial base
-- statement:
--   Every correction of a nontrivial lifted base class obeys the HHO20
--   cohomology-weight alternative.  The proof selects a full-weight-minimal
--   correction, normalizes it without changing its representative, applies the
--   shadow dichotomy, and transfers the resulting lower bound back to the
--   arbitrary correction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2661-L2755
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2661-L2755

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.weight_bound_for_all_corrections_of_nontrivial_base
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (hx : IsNontrivialBaseCohomology baseSample x)
    (hDelta : 0 < Delta)
    (hDegree : RandomBase.HasDegreeWindows (Delta := Delta) baseSample)
    (hExpansion :
      RandomBase.HasStrongSmallSetExpansion (Delta := Delta) baseSample)
    (v : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell)))) :
    Fintype.card (ZMod (ell * ell)) ≤
        2 * HammingWeight
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) v) ∨
      6 * r <
        100000 * Delta *
          HammingWeight
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample) v) := by sorry
