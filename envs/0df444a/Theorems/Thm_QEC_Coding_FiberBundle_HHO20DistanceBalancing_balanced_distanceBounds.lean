-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_balanced_distanceBounds
-- name    : QEC.Coding.FiberBundle.HHO20DistanceBalancing.balanced_distanceBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:39:40.158418+00:00
-- url     : https://prove2.me/theorems/1c2d37ea-7f57-43a4-8191-cdbade5d61ff
-- title:
--   HHO20 Distance Balancing: balanced distance Bounds
-- statement:
--   Finite HHO20--EKZ distance theorem.  The only hypotheses are properties
--   of concrete construction witnesses; the hierarchy theorem below selects
--   those witnesses without assumptions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/DistanceBalancing.lean#L155-L229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/DistanceBalancing.lean#L155-L229

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_CohomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding

theorem QEC.Coding.FiberBundle.HHO20DistanceBalancing.balanced_distanceBounds
    {rMain typeCount ell DeltaMain rBalance DeltaBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance)
    (hDeltaMain : 1 ≤ DeltaMain)
    (hMainGood : RandomBase.IsFullyGood
      (Delta := DeltaMain) baseSample)
    (hLTC : TwistGraph.HasHHO20LocalTestability
      DeltaMain baseSample twistSample)
    (hDeltaBalance : 1 ≤ DeltaBalance)
    (hBalanceGood : RandomBase.IsFullyGood
      (Delta := DeltaBalance) balanceSample) :
    MiddleHomologyDistanceAtLeast
        (DistanceBalancing.chainComplex
          (balancedData baseSample twistSample balanceSample))
        (((4 * rBalance) / 5) *
          mainReducedCohomologyDistance rMain ell DeltaMain) ∧
      MiddleCohomologyDistanceAtLeast
        (DistanceBalancing.chainComplex
          (balancedData baseSample twistSample balanceSample))
        (mainReducedHomologyDistance rMain ell DeltaMain) := by sorry
