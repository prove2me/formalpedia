-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_overlap_projector_tensor_block_lifted_coefficient_factorization
-- name    : QEC.Bounds.BPTCommutingProjectorModel.overlap_projector_tensor_block_lifted_coefficient_factorization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T13:26:31.135935+00:00
-- url     : https://prove2.me/theorems/73007f7c-768d-4f5a-9671-3078dd78c603
-- title:
--   BPTCommuting Projector Model: overlap projector tensor block lifted coefficient factorization
-- statement:
--   Lift the common isotypic unitary to the ambient multiplicity universe while
--   preserving both coefficient-side BV03 tensor actions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4445-L4525
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4445-L4525

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

theorem QEC.Bounds.BPTCommutingProjectorModel.overlap_projector_tensor_block_lifted_coefficient_factorization
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B)
    (n : Nat) (W : Submodule (leftInteractionAlgebra P) B)
    (hW : IsSimpleModule (leftInteractionAlgebra P) W)
    (e : component.1 ≃ₗ[leftInteractionAlgebra P] (Fin n → W)) :
    ∃ U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (W.restrictScalars Complex ⊗[Complex] isotypicLiftedMultiplicity.{u} n),
      (∀ a a' : A,
        U.conjOperator
          (isotypicLeftAction (leftInteractionAlgebra P) component
            ⟨leftInteractionCoefficient P a a',
              leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩) =
          TensorProduct.map
            (isotypicLeftActionOnSimple (leftInteractionAlgebra P) W
              ⟨leftInteractionCoefficient P a a',
                leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩)
            (1 : Semantics.Operator (isotypicLiftedMultiplicity.{u} n))) ∧
      (∀ c c' : C, ∃ R : Semantics.Operator (isotypicLiftedMultiplicity.{u} n),
        U.conjOperator
          (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
            component c c') =
          TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex)) R) := by sorry
