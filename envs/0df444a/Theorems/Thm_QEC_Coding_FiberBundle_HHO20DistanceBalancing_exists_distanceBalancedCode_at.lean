-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_exists_distanceBalancedCode_at
-- name    : QEC.Coding.FiberBundle.HHO20DistanceBalancing.exists_distanceBalancedCode_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:16:39.791827+00:00
-- url     : https://prove2.me/theorems/b7e447c7-7594-40ea-9f5d-5e9f424018a2
-- title:
--   HHO20 Distance Balancing: exists distance Balanced Code at
-- statement:
--   Assumption-free existence of the finite distance-balanced code at every
--   hierarchy index `s ≥ 200`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/DistanceBalancing.lean#L365-L478
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/DistanceBalancing.lean#L365-L478

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_CohomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding

theorem QEC.Coding.FiberBundle.HHO20DistanceBalancing.exists_distanceBalancedCode_at
    (s : Nat) (hs : 200 ≤ s) :
    letI : NeZero (RandomPartition.hho20TypeCount (2 * s)) :=
      ⟨RandomPartition.hho20TypeCount_ne_zero (2 * s) (by omega)⟩
    letI : NeZero (RandomPartition.hho20FiberLength (2 * s)) :=
      ⟨by
        have := RandomPartition.hho20_fiberLength_ge (2 * s) (by omega)
        omega⟩
    letI : NeZero (RandomPartition.hho20FiberLength (2 * s) - 1) :=
      ⟨by
        have := RandomPartition.hho20_fiberLength_ge (2 * s) (by omega)
        omega⟩
    ∃ (baseSample : RandomBase.Sample
          (RandomPartition.hho20BaseScale (2 * s)))
        (twistSample : RandomTwist.Sample
          (RandomPartition.hho20BaseScale (2 * s))
          (RandomPartition.hho20TypeCount (2 * s))
          (RandomPartition.hho20FiberLength (2 * s)))
        (balanceSample : RandomBase.Sample
          (RandomPartition.hho20BaseScale s)),
      (MiddleHomologyDistanceAtLeast
          (DistanceBalancing.chainComplex
            (balancedData baseSample twistSample balanceSample))
          (balancedHomologyDistanceAt s) ∧
        MiddleCohomologyDistanceAtLeast
          (DistanceBalancing.chainComplex
            (balancedData baseSample twistSample balanceSample))
          (balancedCohomologyDistanceAt s)) ∧
        Fintype.card
            (DistanceBalancing.QubitIndex
              (MainQubit baseSample twistSample)
              (MainCZero baseSample twistSample)
              (BalanceBit balanceSample) (BalanceCheck balanceSample)) ≤
          balancedBlocklengthUpperAt s ∧
        RandomPartition.hho20BaseScale (2 * s) *
            RandomPartition.hho20BaseScale s ≤
          Module.finrank (ZMod 2)
            (DistanceBalancing.chainComplex
              (balancedData baseSample twistSample balanceSample)).middleHomology ∧
        RandomBase.IsFullyGood
          (Delta := RandomPartition.hho20DegreeScale (2 * s)) baseSample ∧
        TwistGraph.HasHHO20LocalTestability
          (RandomPartition.hho20DegreeScale (2 * s))
          baseSample twistSample ∧
        RandomBase.IsFullyGood
          (Delta := RandomPartition.hho20DegreeScale s) balanceSample := by sorry
