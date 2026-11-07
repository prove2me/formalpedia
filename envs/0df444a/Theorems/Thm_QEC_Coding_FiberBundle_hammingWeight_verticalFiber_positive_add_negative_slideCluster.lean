-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_verticalFiber_positive_add_negative_slideCluster
-- name    : QEC.Coding.FiberBundle.hammingWeight_verticalFiber_positive_add_negative_slideCluster
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:53:23.965268+00:00
-- url     : https://prove2.me/theorems/43bb7f78-fd41-4a26-ac33-0cd4de6a584f
-- title:
--   Fiber Bundle: hamming Weight vertical Fiber positive add negative slide Cluster
-- statement:
--   The abstract backward toggle above is exactly the vertical sector of the
--   explicit negative cluster slide.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3442-L3469
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3442-L3469

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_verticalFiber_positive_add_negative_slideCluster
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (root : Fin (4 * r) × ZMod (ell * ell))
    (a : Fin (3 * r)) :
    HammingWeight
        (verticalFiber
          (oneStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root)) a) +
      HammingWeight
        (verticalFiber
          (negativeStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root)) a) =
      2 * HammingWeight (verticalFiber z a) := by sorry
