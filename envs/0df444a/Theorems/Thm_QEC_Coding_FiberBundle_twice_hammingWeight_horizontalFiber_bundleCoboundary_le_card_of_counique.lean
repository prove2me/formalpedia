-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_twice_hammingWeight_horizontalFiber_bundleCoboundary_le_card_of_counique
-- name    : QEC.Coding.FiberBundle.twice_hammingWeight_horizontalFiber_bundleCoboundary_le_card_of_counique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:53:44.984388+00:00
-- url     : https://prove2.me/theorems/2a435a00-e89e-4a67-be0f-645c9ab732f1
-- title:
--   Fiber Bundle: twice hamming Weight horizontal Fiber bundle Coboundary le card of counique
-- statement:
--   At a counique base variable, any fiberwise-normalized zero-cell word produces
--   a horizontal coboundary fiber of weight at most half the fiber size.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L947-L971
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L947-L971

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.twice_hammingWeight_horizontalFiber_bundleCoboundary_le_card_of_counique
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hu : C0FibersNormalized u)
    (b : Fin (4 * r))
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample (c0Shadow u)) :
    2 * HammingWeight
        (horizontalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u) b) ≤
      Fintype.card (ZMod (ell * ell)) := by sorry
