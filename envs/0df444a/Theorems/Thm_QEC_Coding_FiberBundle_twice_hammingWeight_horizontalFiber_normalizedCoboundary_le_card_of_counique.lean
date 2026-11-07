-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_twice_hammingWeight_horizontalFiber_normalizedCoboundary_le_card_of_counique
-- name    : QEC.Coding.FiberBundle.twice_hammingWeight_horizontalFiber_normalizedCoboundary_le_card_of_counique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:56:42.040144+00:00
-- url     : https://prove2.me/theorems/d4543aba-eb51-40b1-8a6b-55ad7a7a6bd5
-- title:
--   Fiber Bundle: twice hamming Weight horizontal Fiber normalized Coboundary le card of counique
-- statement:
--   A counique base variable sees at most half a fiber of the coboundary of the
--   explicitly normalized zero-cell word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L977-L996
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L977-L996

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.twice_hammingWeight_horizontalFiber_normalizedCoboundary_le_card_of_counique
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (b : Fin (4 * r))
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample
      (c0Shadow (normalizeC0Fibers u))) :
    2 * HammingWeight
        (horizontalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (normalizeC0Fibers u)) b) ≤
      Fintype.card (ZMod (ell * ell)) := by sorry
