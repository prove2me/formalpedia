-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypic_tensor_unitary_intertwiner
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypic_tensor_unitary_intertwiner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T13:26:16.146444+00:00
-- url     : https://prove2.me/theorems/1badb294-59a6-4749-9678-0e320cb02364
-- title:
--   BPTCommuting Projector Model: isotypic tensor unitary intertwiner
-- statement:
--   The polar-normalized isotypic and copy coordinates compose to a unitary which
--   transports every element of the left interaction algebra to the literal left
--   tensor-factor action.  Both coefficient-side BV03 equations use this same
--   transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4032-L4074
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4032-L4074

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypic_tensor_unitary_intertwiner
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (component : isotypicComponents S B) (n : Nat) (W : Submodule S B)
    (e : component.1 ≃ₗ[S] (Fin n → W)) :
    ∃ U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)),
      ∀ operator : S,
        U.conjOperator (isotypicLeftAction S component operator) =
          isotypicTensorLeftAction S W n operator := by sorry
