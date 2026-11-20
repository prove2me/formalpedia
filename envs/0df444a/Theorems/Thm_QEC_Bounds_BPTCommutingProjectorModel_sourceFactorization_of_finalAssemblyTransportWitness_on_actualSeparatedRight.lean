-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_sourceFactorization_of_finalAssemblyTransportWitness_on_actualSeparatedRight
-- name    : QEC.Bounds.BPTCommutingProjectorModel.sourceFactorization_of_finalAssemblyTransportWitness_on_actualSeparatedRight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T07:53:46.280527+00:00
-- url     : https://prove2.me/theorems/7b043732-1b27-43d1-8219-f017ce880d74
-- title:
--   BPTCommuting Projector Model: source Factorization of final Assembly Transport Witness on actual Separated Right
-- statement:
--   The BPTCommuting Projector Model construction uses the source Factorization of final Assembly Transport Witness on actual Separated Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorizations/TransportWitnessFactorization.lean#L28-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorizations/TransportWitnessFactorization.lean#L28-L67

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorizations_ExteriorFactorization
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransportCore
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorizations_TransportWitnessFactorization
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

theorem QEC.Bounds.BPTCommutingProjectorModel.sourceFactorization_of_finalAssemblyTransportWitness_on_actualSeparatedRight
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
    (hwitness : FinalAssemblyTransportWitness
      M left bcomponent ccomponent WB WC UB UC P_D) :
    ∀ (A : Semantics.Operator (M.regionSubsystem left).selectedSystem)
      (B : Semantics.Operator (M.regionSubsystem right).selectedSystem),
      ∃ coefficient : Complex,
        M.fullCodeProjector * (M.regionSubsystem left).extendLocalToRegister A *
            (M.regionSubsystem right).extendLocalToRegister B * M.fullCodeProjector =
          coefficient •
            (M.fullCodeProjector * (M.regionSubsystem right).extendLocalToRegister B *
              M.fullCodeProjector) := by sorry
