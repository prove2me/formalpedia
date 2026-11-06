-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicCopyTensorCoordinates_matrix_intertwines
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicCopyTensorCoordinates_matrix_intertwines
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:41:25.64336+00:00
-- url     : https://prove2.me/theorems/95899dbf-25c1-4384-8d52-71a248c77a44
-- title:
--   BPTCommuting Projector Model: isotypic Copy Tensor Coordinates matrix intertwines
-- statement:
--   Canonical copy-to-tensor coordinates carry a multiplicity matrix precisely to
--   the right tensor factor.  This is the concrete conversion from Schur's matrix
--   description of a commutant to `1 tensor matrixOperator`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3604-L3636
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3604-L3636

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicCopyTensorCoordinates_matrix_intertwines
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (matrix : Matrix (Fin n) (Fin n) Complex) :
    (isotypicCopyTensorCoordinates S W n).toLinearMap.comp
        (isotypicMultiplicityMatrixActionOnCopies S W n matrix) =
      (TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex))
        (isotypicMultiplicityMatrixOperator n matrix)).comp
        (isotypicCopyTensorCoordinates S W n).toLinearMap := by sorry
