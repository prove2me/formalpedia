-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_sourceFactorization_of_finalAssemblyWitness
-- name    : QEC.Bounds.BPTCommutingProjectorModel.sourceFactorization_of_finalAssemblyWitness
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T07:41:07.951527+00:00
-- url     : https://prove2.me/theorems/a293b0cd-06eb-4c6b-9341-20d1304de323
-- title:
--   BPTCommuting Projector Model: source Factorization of final Assembly Witness
-- statement:
--   The BPTCommuting Projector Model construction uses the source Factorization of final Assembly Witness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/Core.lean#L23-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/Core.lean#L23-L118

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_SourceLift
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_Core
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 3000000
set_option maxRecDepth 2000

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.sourceFactorization_of_finalAssemblyWitness
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))
    (phi : Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
    (n0 : isotypicLiftedMultiplicity.{0} nB)
    (c0 : WC.restrictScalars Complex)
    (U : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex))
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex)))
    (hphi : ‖phi‖ = 1) (hn0 : ‖n0‖ = 1) (hc0 : ‖c0‖ = 1)
    (htransport :
      let pB := bcomponent.1.restrictScalars Complex
      let pC := ccomponent.1.restrictScalars Complex
      let Uglobal := M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U
      let Eout := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
      let Pproduct : Semantics.Operator
          (Semantics.CompositeSystem
            (Semantics.CompositeSystem
              (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
              (isotypicLiftedMultiplicity.{0} nB))
            (Semantics.CompositeSystem (WC.restrictScalars Complex)
              (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
                (M.fourFactorD region)))) :=
        rankOneTensorOperator
          (phi ⊗ₜ[Complex] n0 : Semantics.CompositeSystem
            (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
            (isotypicLiftedMultiplicity.{0} nB))
          (rankOneTensorOperator c0 P_D)
      (M.fourFactorTransport region).conjOperator
          (Uglobal.conjOperator M.fullCodeProjector) =
        Eout.comp (Pproduct.comp (LinearMap.adjoint Eout)))
    (A : Semantics.Operator (M.regionSubsystem region).selectedSystem)
    (B : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem)
    (hBfixed :
      (M.activeSectorBoundaryGlobalUnitary region
        (bcomponent.1.restrictScalars Complex) (ccomponent.1.restrictScalars Complex) UB UC U).conjOperator
          ((M.regionSubsystem (M.exterior region)).extendLocalToRegister B) =
        (M.regionSubsystem (M.exterior region)).extendLocalToRegister B) :
    ∃ coefficient : Complex,
      M.fullCodeProjector * (M.regionSubsystem region).extendLocalToRegister A *
          (M.regionSubsystem (M.exterior region)).extendLocalToRegister B *
          M.fullCodeProjector = coefficient •
        (M.fullCodeProjector *
          (M.regionSubsystem (M.exterior region)).extendLocalToRegister B *
          M.fullCodeProjector) := by sorry
