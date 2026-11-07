-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_commuting_overlap_tensor_block_coefficient_factorization
-- name    : QEC.Bounds.BPTCommutingProjectorModel.commuting_overlap_tensor_block_coefficient_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:43:36.257974+00:00
-- url     : https://prove2.me/theorems/9003eb29-66e8-426f-9b1e-75275adb146a
-- title:
--   BPTCommuting Projector Model: commuting overlap tensor block coefficient factorization
-- statement:
--   The direct-sum/isotypic part of the BV03 decomposition together with the
--   unitary tensor-factor coefficient equations on every summand.  Unlike a joint
--   spectral decomposition, each summand has one common transport carrying the
--   left interaction algebra to the first tensor factor and the commuting right
--   interaction algebra to the second.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4838-L4875
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4838-L4875

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

theorem QEC.Bounds.BPTCommutingProjectorModel.commuting_overlap_tensor_block_coefficient_factorization
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q)) :
    DirectSum.IsInternal (fun component : isotypicComponents (leftInteractionAlgebra P) B =>
      component.1) ∧
      ∀ component : isotypicComponents (leftInteractionAlgebra P) B,
        ∃ (n : Nat) (_ : NeZero n) (W : Submodule (leftInteractionAlgebra P) B)
          (hW : IsSimpleModule (leftInteractionAlgebra P) W)
          (e : component.1 ≃ₗ[leftInteractionAlgebra P] (Fin n → W))
          (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
            (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n))),
          (∀ a a' : A,
            U.conjOperator
              (isotypicLeftAction (leftInteractionAlgebra P) component
                ⟨leftInteractionCoefficient P a a',
                  leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩) =
              isotypicTensorLeftAction (leftInteractionAlgebra P) W n
                ⟨leftInteractionCoefficient P a a',
                  leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩) ∧
          (∀ c c' : C, ∃ R : Semantics.Operator (EuclideanSpace Complex (Fin n)),
            U.conjOperator
              (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
                component c c') =
              TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex)) R) := by sorry
