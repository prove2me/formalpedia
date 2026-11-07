-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_overlap_projector_tensor_blocks_single_sector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.overlap_projector_tensor_blocks_single_sector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:26:54.097613+00:00
-- url     : https://prove2.me/theorems/00e656a7-74e8-456e-b652-ffbbde3d2c6f
-- title:
--   BPTCommuting Projector Model: overlap projector tensor blocks single sector
-- statement:
--   The concrete BV03 tensor-block equality on one left-isotypic sector.  The
--   same boundary unitary sends the compressed left overlap projector to
--   `P_left tensor 1` and the compressed right overlap projector to
--   `1 tensor Q_right`, with the displayed source parenthesizations retained.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4654-L4687
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4654-L4687

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

theorem QEC.Bounds.BPTCommutingProjectorModel.overlap_projector_tensor_blocks_single_sector
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B)
    (n : Nat) [NeZero n] (W : Submodule (leftInteractionAlgebra P) B)
    (hW : IsSimpleModule (leftInteractionAlgebra P) W)
    (e : component.1 ≃ₗ[leftInteractionAlgebra P] (Fin n → W)) :
    ∃ (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
        (W.restrictScalars Complex ⊗[Complex] isotypicLiftedMultiplicity.{u} n))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem A (W.restrictScalars Complex)))
      (Qright : Semantics.Operator
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{u} n) C)),
      (unitaryLTensor A U).conjOperator
        (overlapProjectorOnIsotypicComponent P component) =
        rightTensorExtensionAfterLeft A (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{u} n) Pleft ∧
      (unitaryRTensor U C).conjOperator
        (overlapRightProjectorOnIsotypicComponent P Q component) =
        leftTensorExtensionBeforeRight (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{u} n) C Qright := by sorry
