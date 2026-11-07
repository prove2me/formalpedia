-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_exists_slideCluster_direction_hammingWeight_le
-- name    : QEC.Coding.FiberBundle.exists_slideCluster_direction_hammingWeight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:10:20.672751+00:00
-- url     : https://prove2.me/theorems/028da21d-312f-4152-b78d-b2a7ff4f12ce
-- title:
--   Fiber Bundle: exists slide Cluster direction hamming Weight le
-- statement:
--   Consequently at least one of the two explicit sliding directions does not
--   increase total Hamming weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3591-L3615
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3591-L3615

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.exists_slideCluster_direction_hammingWeight_le
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
            baseSample twistSample z root)) ≤ HammingWeight z ∨
      HammingWeight
        (negativeStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) ≤ HammingWeight z := by sorry
