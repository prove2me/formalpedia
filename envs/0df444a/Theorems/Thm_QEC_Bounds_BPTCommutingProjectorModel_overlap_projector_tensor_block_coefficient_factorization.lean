-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_overlap_projector_tensor_block_coefficient_factorization
-- name    : QEC.Bounds.BPTCommutingProjectorModel.overlap_projector_tensor_block_coefficient_factorization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T13:09:33.090308+00:00
-- url     : https://prove2.me/theorems/17824ec0-4329-4abf-b426-177adc9aa417
-- title:
--   BPTCommuting Projector Model: overlap projector tensor block coefficient factorization
-- statement:
--   The concrete BV03 tensor-block equation on one left-isotypic sector.  The same
--   unitary sends every displayed left coefficient to `L tensor 1` and every
--   displayed right coefficient to `1 tensor R`; the latter is obtained by the
--   commutant matrix factorization, rather than by a joint spectral decomposition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4368-L4439
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4368-L4439

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

theorem QEC.Bounds.BPTCommutingProjectorModel.overlap_projector_tensor_block_coefficient_factorization
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
      (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)),
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
