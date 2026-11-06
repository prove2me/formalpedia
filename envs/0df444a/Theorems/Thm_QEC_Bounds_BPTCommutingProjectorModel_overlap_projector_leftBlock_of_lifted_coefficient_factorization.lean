-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_overlap_projector_leftBlock_of_lifted_coefficient_factorization
-- name    : QEC.Bounds.BPTCommutingProjectorModel.overlap_projector_leftBlock_of_lifted_coefficient_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:26:49.752323+00:00
-- url     : https://prove2.me/theorems/73ecfd2e-7a09-4dea-9fac-90448c24772b
-- title:
--   BPTCommuting Projector Model: overlap projector left Block of lifted coefficient factorization
-- statement:
--   Reconstruct the left projector block from a fixed lifted coefficient transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4528-L4585
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4528-L4585

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

theorem QEC.Bounds.BPTCommutingProjectorModel.overlap_projector_leftBlock_of_lifted_coefficient_factorization
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B)
    (n : Nat) [NeZero n] (W : Submodule (leftInteractionAlgebra P) B)
    (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (W.restrictScalars Complex ⊗[Complex] isotypicLiftedMultiplicity.{u} n))
    (hleft : ∀ a a' : A,
      U.conjOperator
          (isotypicLeftAction (leftInteractionAlgebra P) component
            ⟨leftInteractionCoefficient P a a',
              leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩) =
        TensorProduct.map
          (isotypicLeftActionOnSimple (leftInteractionAlgebra P) W
            ⟨leftInteractionCoefficient P a a',
              leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩)
          (1 : Semantics.Operator (isotypicLiftedMultiplicity.{u} n))) :
    ∃ Pleft : Semantics.Operator (Semantics.CompositeSystem A (W.restrictScalars Complex)),
      (unitaryLTensor A U).conjOperator
          (overlapProjectorOnIsotypicComponent P component) =
        rightTensorExtensionAfterLeft A (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{u} n) Pleft := by sorry
