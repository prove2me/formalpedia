-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_exists_slidHomologyRepresentative
-- name    : QEC.Coding.FiberBundle.exists_slidHomologyRepresentative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:54:16.871179+00:00
-- url     : https://prove2.me/theorems/05c0f925-13b4-43b8-b420-fbd5da708fba
-- title:
--   Fiber Bundle: exists slid Homology Representative
-- statement:
--   Packaged sliding reduction for the homology-distance argument.  All
--   downstream invariants and the vertical error-shadow bound are exposed
--   together on one construction-owned representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4322-L4368
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4322-L4368

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.exists_slidHomologyRepresentative
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
      homologyBaseProjection z' = homologyBaseProjection z ∧
      (z' ∉
          (chainComplex
            (RandomTwist.fiberBundleData baseSample twistSample)
            ).middleBoundaryCode.carrier ↔
        z ∉
          (chainComplex
            (RandomTwist.fiberBundleData baseSample twistSample)
            ).middleBoundaryCode.carrier) ∧
      IsHorizontallyResidueNormalized z' ∧
      ell *
          (horizontalBoundaryShadow baseSample twistSample
            (horizontalComponent z')).card ≤
        HammingWeight (verticalComponent z') := by sorry
