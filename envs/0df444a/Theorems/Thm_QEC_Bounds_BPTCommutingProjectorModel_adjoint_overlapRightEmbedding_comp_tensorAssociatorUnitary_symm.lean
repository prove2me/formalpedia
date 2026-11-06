-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_overlapRightEmbedding_comp_tensorAssociatorUnitary_symm
-- name    : QEC.Bounds.BPTCommutingProjectorModel.adjoint_overlapRightEmbedding_comp_tensorAssociatorUnitary_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:24:02.972883+00:00
-- url     : https://prove2.me/theorems/ff045a66-c325-403a-8199-471fb3d0d085
-- title:
--   BPTCommuting Projector Model: adjoint overlap Right Embedding comp tensor Associator Unitary symm
-- statement:
--   Taking adjoints gives the companion right-coefficient associator identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1758-L1778
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1758-L1778

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.adjoint_overlapRightEmbedding_comp_tensorAssociatorUnitary_symm
    (W N C : Type u)
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (c : C) :
    (LinearMap.adjoint
      (overlapRightEmbedding (Semantics.CompositeSystem W N) C c)).comp
      (tensorAssociatorUnitary W N C).symm.toLinearEquiv.toLinearMap =
        TensorProduct.map (1 : Semantics.Operator W)
          (LinearMap.adjoint (overlapRightEmbedding N C c)) := by sorry
