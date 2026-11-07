-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_positive_eq_and_negative_eq_of_homologyClassWeightMinimal
-- name    : QEC.Coding.FiberBundle.hammingWeight_positive_eq_and_negative_eq_of_homologyClassWeightMinimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:54:07.851845+00:00
-- url     : https://prove2.me/theorems/17cc09b6-c032-4d31-8e17-2fdf80d2da5b
-- title:
--   Fiber Bundle: hamming Weight positive eq and negative eq of homology Class Weight Minimal
-- statement:
--   At a minimum-weight representative, both cluster-slide directions preserve
--   weight exactly; neither direction can lie below the class minimum, and their
--   sum is already bounded above by twice that minimum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4026-L4074
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4026-L4074

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_positive_eq_and_negative_eq_of_homologyClassWeightMinimal
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
    (hMinimal :
      IsHomologyClassWeightMinimal baseSample twistSample z)
    (root : Fin (4 * r) × ZMod (ell * ell)) :
    HammingWeight
        (oneStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) =
        HammingWeight z ∧
    HammingWeight
        (negativeStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) =
        HammingWeight z := by sorry
