-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_verticalComponent_positive_add_negative_slideCluster
-- name    : QEC.Coding.FiberBundle.hammingWeight_verticalComponent_positive_add_negative_slideCluster
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:53:30.660304+00:00
-- url     : https://prove2.me/theorems/afe17a47-7e6a-4347-a87a-b852a8c8428f
-- title:
--   Fiber Bundle: hamming Weight vertical Component positive add negative slide Cluster
-- statement:
--   Positive and negative cluster slides have complementary total vertical cost.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3472-L3521
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3472-L3521

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_verticalComponent_positive_add_negative_slideCluster
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
    (root : Fin (4 * r) × ZMod (ell * ell)) :
    HammingWeight
        (verticalComponent
          (oneStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root))) +
      HammingWeight
        (verticalComponent
          (negativeStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root))) =
      2 * HammingWeight (verticalComponent z) := by sorry
