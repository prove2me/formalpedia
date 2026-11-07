-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_positive_add_negative_slideCluster_le
-- name    : QEC.Coding.FiberBundle.hammingWeight_positive_add_negative_slideCluster_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:47:49.332254+00:00
-- url     : https://prove2.me/theorems/fbf8abc9-52f3-484f-9995-ffb45d1bcbf7
-- title:
--   Fiber Bundle: hamming Weight positive add negative slide Cluster le
-- statement:
--   The two explicit directions together cost at most twice the original total
--   weight: horizontally each direction is nonincreasing, while vertically their
--   costs are exactly complementary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3528-L3585
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3528-L3585

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_positive_add_negative_slideCluster_le
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
        (oneStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) +
      HammingWeight
        (negativeStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) ≤
      2 * HammingWeight z := by sorry
