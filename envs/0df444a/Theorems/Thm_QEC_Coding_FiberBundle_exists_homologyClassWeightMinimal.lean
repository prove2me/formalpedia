-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_exists_homologyClassWeightMinimal
-- name    : QEC.Coding.FiberBundle.exists_homologyClassWeightMinimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:53:54.49478+00:00
-- url     : https://prove2.me/theorems/294a433e-b2cb-4f1c-9239-dc9f3e238097
-- title:
--   Fiber Bundle: exists homology Class Weight Minimal
-- statement:
--   Every bundle cycle has a no-heavier, homologous representative that minimizes
--   weight over its entire degree-two-boundary coset.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3943-L4019
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3943-L4019

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.exists_homologyClassWeightMinimal
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
        ).middleCycleCode.carrier) :
    ∃ z',
      z' ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier ∧
      HammingWeight z' ≤ HammingWeight z ∧
      z' + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ∧
      IsHomologyClassWeightMinimal baseSample twistSample z' := by sorry
