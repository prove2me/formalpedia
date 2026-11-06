-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_commuting_overlap_block_factorization
-- name    : QEC.Bounds.BPTCommutingProjectorModel.commuting_overlap_block_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:09:33.246679+00:00
-- url     : https://prove2.me/theorems/0d44eb46-e00d-432c-bcae-c34f471da842
-- title:
--   BPTCommuting Projector Model: commuting overlap block factorization
-- statement:
--   The finite-dimensional BV03 overlap decomposition in its concrete
--   interaction-algebra form.  The first conjunct is the direct sum of
--   left-isotypic boundary sectors.  In every sector an actual simple factor
--   `W` and a finite multiplicity coordinate are exhibited.  The two displayed
--   actions are the coefficient-level tensor-block equations: every left
--   coefficient acts only on `W`, while every right coefficient acts only by a
--   scalar matrix on the multiplicity coordinate.  These separate equations are
--   the input for reconstructing the two overlapping projectors blockwise; they
--   are stronger than a joint spectral decomposition of global projectors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4732-L4805
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4732-L4805

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

theorem QEC.Bounds.BPTCommutingProjectorModel.commuting_overlap_block_factorization
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
          (e : component.1 ≃ₗ[leftInteractionAlgebra P] (Fin n → W)),
          (∀ a a' : A, ∀ (vector : component.1) (row : Fin n),
            e ((⟨leftInteractionCoefficient P a a',
              leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩ :
                leftInteractionAlgebra P) • vector) row =
              (⟨leftInteractionCoefficient P a a',
                leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩ :
                  leftInteractionAlgebra P) • e vector row) ∧
          (∀ c c' : C, ∃ matrix : Matrix (Fin n) (Fin n) Complex,
            ∀ (vector : component.1) (row : Fin n),
              e (rightInteractionCoefficientOnIsotypicComponent P Q hselfAdjoint hcommute
                component c c' vector) row =
                ∑ column, matrix row column • e vector column) := by sorry
