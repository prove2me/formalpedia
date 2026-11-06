-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_eraseC0Fiber_lt_of_four_fifths
-- name    : QEC.Coding.FiberBundle.hammingWeight_eraseC0Fiber_lt_of_four_fifths
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:57:23.833943+00:00
-- url     : https://prove2.me/theorems/755b0ee7-55d5-4c43-91da-7e96ed5cff0a
-- title:
--   Fiber Bundle: hamming Weight erase C0 Fiber lt of four fifths
-- statement:
--   The HHO20 `C ∩ x = ∅` erasure move strictly decreases the full representative
--   weight, not only its horizontal sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1956-L1995
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1956-L1995

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_eraseC0Fiber_lt_of_four_fifths
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a : Fin (3 * r))
    (ha : a ∈ c0Shadow u)
    (hCounique :
      4 * RandomBase.checkDegree baseSample a <
        5 * RandomBase.couniqueDegree baseSample (c0Shadow u) a)
    (hDisjoint :
      ∀ b ∈ RandomBase.couniqueNeighbors baseSample (c0Shadow u),
        x b = 0) :
    HammingWeight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (eraseC0Fiber u a)) <
      HammingWeight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u) := by sorry
