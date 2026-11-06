-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicMultiplicityMatrixOperator_apply
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicMultiplicityMatrixOperator_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:25:37.115821+00:00
-- url     : https://prove2.me/theorems/4992ad8a-cfbb-4e54-93e4-059baa5f3f34
-- title:
--   BPTCommuting Projector Model: isotypic Multiplicity Matrix Operator apply
-- statement:
--   The matrix operator has the expected coordinate action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3549-L3554
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3549-L3554

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicMultiplicityMatrixOperator_apply (n : Nat)
    (matrix : Matrix (Fin n) (Fin n) Complex)
    (vector : EuclideanSpace Complex (Fin n)) :
    isotypicMultiplicityMatrixOperator n matrix vector =
      (EuclideanSpace.equiv (Fin n) Complex).symm (Matrix.mulVec matrix vector) := by sorry
