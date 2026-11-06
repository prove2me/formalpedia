-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_overlapRightEmbedding_comp_tensorMap_left_adjoint_hom
-- name    : QEC.Bounds.BPTCommutingProjectorModel.adjoint_overlapRightEmbedding_comp_tensorMap_left_adjoint_hom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:25:06.4262+00:00
-- url     : https://prove2.me/theorems/fded1830-0900-443f-a46c-cd5c06564d86
-- title:
--   BPTCommuting Projector Model: adjoint overlap Right Embedding comp tensor Map left adjoint hom
-- statement:
--   The adjoint form of fixed-right embedding naturality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3179-L3191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3179-L3191

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

theorem QEC.Bounds.BPTCommutingProjectorModel.adjoint_overlapRightEmbedding_comp_tensorMap_left_adjoint_hom
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (c : C) (Z : A →ₗ[Complex] B) :
    (LinearMap.adjoint (overlapRightEmbedding A C c)).comp
      (TensorProduct.map (LinearMap.adjoint Z) (1 : Semantics.Operator C)) =
        (LinearMap.adjoint Z).comp (LinearMap.adjoint (overlapRightEmbedding B C c)) := by sorry
