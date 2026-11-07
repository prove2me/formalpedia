-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_weightedHammingCost_shiftCluster_add_hammingWeight
-- name    : QEC.Coding.FiberBundle.weightedHammingCost_shiftCluster_add_hammingWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:51:22.355855+00:00
-- url     : https://prove2.me/theorems/3e711374-cbbb-4b83-aadc-b2739e8c1650
-- title:
--   Fiber Bundle: weighted Hamming Cost shift Cluster add hamming Weight
-- statement:
--   Shifting a nonzero-residue cluster forward lowers its weighted residue cost
--   by exactly the cluster's Hamming weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1563-L1626
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1563-L1626

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.weightedHammingCost_shiftCluster_add_hammingWeight
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root : Fin (4 * r) × ZMod (ell * ell))
    (hRootResidue : fiberResidue ell root.2 ≠ 0) :
    WeightedHammingCost
        (fun bi => (-fiberResidue ell bi.2).val)
        (shiftHorizontalSubchain (ell * ell)
          (horizontalClusterSubchain
            baseSample twistSample z root)) +
      HammingWeight
        (horizontalClusterSubchain
          baseSample twistSample z root) =
    WeightedHammingCost
        (fun bi => (-fiberResidue ell bi.2).val)
        (horizontalClusterSubchain
          baseSample twistSample z root) := by sorry
