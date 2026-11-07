-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalComponent_slideCluster_le
-- name    : QEC.Coding.FiberBundle.hammingWeight_horizontalComponent_slideCluster_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:51:43.68446+00:00
-- url     : https://prove2.me/theorems/47f94a39-82f2-42ab-b153-c8450cd23552
-- title:
--   Fiber Bundle: hamming Weight horizontal Component slide Cluster le
-- statement:
--   In particular, sliding a support-induced cluster never raises horizontal cost.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1800-L1817
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1800-L1817

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_horizontalComponent_slideCluster_le
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root : Fin (4 * r) × ZMod (ell * ell)) :
    HammingWeight
        (horizontalComponent
          (oneStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root))) ≤
      HammingWeight (horizontalComponent z) := by sorry
