-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_sourceFactorization_of_fixedActiveData_on_actualSeparatedRight
-- name    : QEC.Bounds.BPTCommutingProjectorModel.sourceFactorization_of_fixedActiveData_on_actualSeparatedRight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T07:58:48.899173+00:00
-- url     : https://prove2.me/theorems/b2194db4-c1f0-4c2e-aa8a-14619a16bb2c
-- title:
--   BPTCommuting Projector Model: source Factorization of fixed Active Data on actual Separated Right
-- statement:
--   The BPTCommuting Projector Model construction uses the source Factorization of fixed Active Data on actual Separated Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorizations/FixedDataFactorization.lean#L28-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorizations/FixedDataFactorization.lean#L28-L68

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorizations_TransportWitnessFactorization
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransport
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorizations_FixedDataFactorization
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

theorem QEC.Bounds.BPTCommutingProjectorModel.sourceFactorization_of_fixedActiveData_on_actualSeparatedRight
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right)
    (hdisjoint : Disjoint left right)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal left))
      (M.fourFactorB left))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC left))
      (M.fourFactorC left))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal left))
      (M.fourFactorB left))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC left))
      (M.fourFactorC left))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD left)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC left) (M.fourFactorD left))))
    (hfixed : M.FixedActiveDataProductRankOneTensor
      left bcomponent ccomponent WB WC UB UC P_D Qsecond) :
    ∀ (A : Semantics.Operator (M.regionSubsystem left).selectedSystem)
      (B : Semantics.Operator (M.regionSubsystem right).selectedSystem),
      ∃ coefficient : Complex,
        M.fullCodeProjector * (M.regionSubsystem left).extendLocalToRegister A *
            (M.regionSubsystem right).extendLocalToRegister B * M.fullCodeProjector =
          coefficient •
            (M.fullCodeProjector * (M.regionSubsystem right).extendLocalToRegister B *
              M.fullCodeProjector) := by sorry
