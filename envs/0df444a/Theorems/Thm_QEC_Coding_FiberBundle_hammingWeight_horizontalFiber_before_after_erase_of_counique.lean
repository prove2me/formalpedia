-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalFiber_before_after_erase_of_counique
-- name    : QEC.Coding.FiberBundle.hammingWeight_horizontalFiber_before_after_erase_of_counique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:56:34.596663+00:00
-- url     : https://prove2.me/theorems/efbc0c85-d4a4-42ae-8cc9-a048ecd8ee35
-- title:
--   Fiber Bundle: hamming Weight horizontal Fiber before after erase of counique
-- statement:
--   At a counique variable incident to the erased check and disjoint from the base
--   support, the old horizontal fiber has exactly the erased-fiber weight and the
--   new horizontal fiber vanishes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L845-L941
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L845-L941

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_horizontalFiber_before_after_erase_of_counique
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a : Fin (3 * r)) (b : Fin (4 * r))
    (ha : a ∈ c0Shadow u)
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample (c0Shadow u))
    (hab : baseSample (a, b) = true)
    (hxb : x b = 0) :
    HammingWeight
        (horizontalFiber
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u) b) =
        HammingWeight (c0Fiber u a) ∧
      HammingWeight
        (horizontalFiber
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (eraseC0Fiber u a)) b) = 0 := by sorry
