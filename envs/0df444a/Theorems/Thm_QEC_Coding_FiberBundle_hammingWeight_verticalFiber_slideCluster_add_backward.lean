-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_verticalFiber_slideCluster_add_backward
-- name    : QEC.Coding.FiberBundle.hammingWeight_verticalFiber_slideCluster_add_backward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:53:20.909903+00:00
-- url     : https://prove2.me/theorems/61b6e2af-5720-40dc-aa51-a63dc76e5750
-- title:
--   Fiber Bundle: hamming Weight vertical Fiber slide Cluster add backward
-- statement:
--   At every base zero-cell, the positive cluster slide and the complementary
--   backward toggle have vertical weights summing to twice the original vertical
--   fiber weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3400-L3436
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3400-L3436

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_verticalFiber_slideCluster_add_backward
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
        (verticalFiber z a +
          backwardVertexToggle (ell * ell)
            (horizontalChainBoundary baseSample twistSample
              (horizontalClusterSubchain
                baseSample twistSample z root) a)) =
      2 * HammingWeight (verticalFiber z a) := by sorry
