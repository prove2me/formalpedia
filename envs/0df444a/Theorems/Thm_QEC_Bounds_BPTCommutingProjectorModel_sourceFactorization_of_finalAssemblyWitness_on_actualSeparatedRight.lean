-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_sourceFactorization_of_finalAssemblyWitness_on_actualSeparatedRight
-- name    : QEC.Bounds.BPTCommutingProjectorModel.sourceFactorization_of_finalAssemblyWitness_on_actualSeparatedRight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T07:48:45.009185+00:00
-- url     : https://prove2.me/theorems/51de2d11-08ca-4cc3-a06a-a3f76217d8f1
-- title:
--   BPTCommuting Projector Model: source Factorization of final Assembly Witness on actual Separated Right
-- statement:
--   The BPTCommuting Projector Model construction uses the source Factorization of final Assembly Witness on actual Separated Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorizations/ExteriorFactorization.lean#L27-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorizations/ExteriorFactorization.lean#L27-L124

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_Core
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorizations_ExteriorFactorization
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

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.sourceFactorization_of_finalAssemblyWitness_on_actualSeparatedRight
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
    (phi : Semantics.CompositeSystem (M.fourFactorA left) (WB.restrictScalars Complex))
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
      let Uglobal := M.activeSectorBoundaryGlobalUnitary left pB pC UB UC U
      let Eout := M.finalAssemblyOutputEmbedding left bcomponent ccomponent WB WC UB UC
      let Pproduct : Semantics.Operator
          (Semantics.CompositeSystem
            (Semantics.CompositeSystem
              (Semantics.CompositeSystem (M.fourFactorA left) (WB.restrictScalars Complex))
              (isotypicLiftedMultiplicity.{0} nB))
            (Semantics.CompositeSystem (WC.restrictScalars Complex)
              (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
                (M.fourFactorD left)))) :=
        rankOneTensorOperator
          (phi ⊗ₜ[Complex] n0 : Semantics.CompositeSystem
            (Semantics.CompositeSystem (M.fourFactorA left) (WB.restrictScalars Complex))
            (isotypicLiftedMultiplicity.{0} nB))
          (rankOneTensorOperator c0 P_D)
      (M.fourFactorTransport left).conjOperator
          (Uglobal.conjOperator M.fullCodeProjector) =
        Eout.comp (Pproduct.comp (LinearMap.adjoint Eout))) :
    ∀ (A : Semantics.Operator (M.regionSubsystem left).selectedSystem)
      (B : Semantics.Operator (M.regionSubsystem right).selectedSystem),
      ∃ coefficient : Complex,
        M.fullCodeProjector * (M.regionSubsystem left).extendLocalToRegister A *
            (M.regionSubsystem right).extendLocalToRegister B * M.fullCodeProjector =
          coefficient •
            (M.fullCodeProjector * (M.regionSubsystem right).extendLocalToRegister B *
              M.fullCodeProjector) := by sorry
