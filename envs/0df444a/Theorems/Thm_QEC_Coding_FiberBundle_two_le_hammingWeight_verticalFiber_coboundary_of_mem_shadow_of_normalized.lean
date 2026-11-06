-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_two_le_hammingWeight_verticalFiber_coboundary_of_mem_shadow_of_normalized
-- name    : QEC.Coding.FiberBundle.two_le_hammingWeight_verticalFiber_coboundary_of_mem_shadow_of_normalized
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:53:46.946693+00:00
-- url     : https://prove2.me/theorems/4494384d-41ba-4fe4-a2b3-0a2d5e97ffab
-- title:
--   Fiber Bundle: two le hamming Weight vertical Fiber coboundary of mem shadow of normalized
-- statement:
--   Every supported fiber of a fiberwise-normalized zero-cell word contributes at
--   least two vertical cells.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1296-L1319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1296-L1319

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.two_le_hammingWeight_verticalFiber_coboundary_of_mem_shadow_of_normalized
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hu : C0FibersNormalized u)
    (a : Fin (3 * r))
    (ha : a ∈ c0Shadow u) :
    2 ≤ HammingWeight
      (verticalFiber
        (bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample) u) a) := by sorry
