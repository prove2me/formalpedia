-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_overlapLeftEmbedding_comp_tensorMap_right_adjoint_hom
-- name    : QEC.Bounds.BPTCommutingProjectorModel.adjoint_overlapLeftEmbedding_comp_tensorMap_right_adjoint_hom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:25:00.512209+00:00
-- url     : https://prove2.me/theorems/1ec1b9bc-0443-4df8-92a7-88ef28bd93b3
-- title:
--   BPTCommuting Projector Model: adjoint overlap Left Embedding comp tensor Map right adjoint hom
-- statement:
--   The adjoint form of fixed-left embedding naturality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3150-L3162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3150-L3162

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

theorem QEC.Bounds.BPTCommutingProjectorModel.adjoint_overlapLeftEmbedding_comp_tensorMap_right_adjoint_hom
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (a : A) (Z : B →ₗ[Complex] C) :
    (LinearMap.adjoint (overlapLeftEmbedding A B a)).comp
      (TensorProduct.map (1 : Semantics.Operator A) (LinearMap.adjoint Z)) =
        (LinearMap.adjoint Z).comp (LinearMap.adjoint (overlapLeftEmbedding A C a)) := by sorry
