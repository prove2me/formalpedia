-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSimpleCopyTensorCoordinates_matrix_intertwines
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicSimpleCopyTensorCoordinates_matrix_intertwines
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:25:49.023949+00:00
-- url     : https://prove2.me/theorems/f96e838d-9aa3-4dc6-95c4-e4b4da4091fe
-- title:
--   BPTCommuting Projector Model: isotypic Simple Copy Tensor Coordinates matrix intertwines
-- statement:
--   Algebraic multiplicity matrices become literal operators on the right tensor
--   factor under the simple-copy coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3862-L3892
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3862-L3892

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicSimpleCopyTensorCoordinates_matrix_intertwines
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (matrix : Matrix (Fin n) (Fin n) Complex) :
    (isotypicSimpleCopyTensorCoordinates S W n).toLinearMap.comp
        (isotypicMultiplicityMatrixActionOnFunctionCopies S W n matrix) =
      (TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex))
        (isotypicMultiplicityMatrixOperator n matrix)).comp
        (isotypicSimpleCopyTensorCoordinates S W n).toLinearMap := by sorry
