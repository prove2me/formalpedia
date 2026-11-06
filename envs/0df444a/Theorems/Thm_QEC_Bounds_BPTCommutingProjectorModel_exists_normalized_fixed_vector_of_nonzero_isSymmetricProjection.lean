-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_normalized_fixed_vector_of_nonzero_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.exists_normalized_fixed_vector_of_nonzero_isSymmetricProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:10:49.535635+00:00
-- url     : https://prove2.me/theorems/96fab788-29be-4c26-9081-59c3361a318e
-- title:
--   BPTCommuting Projector Model: exists normalized fixed vector of nonzero is Symmetric Projection
-- statement:
--   A nonzero orthogonal projection has a normalized fixed vector in its range.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ResidualProjection.lean#L24-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ResidualProjection.lean#L24-L45

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Tensor
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualProjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.exists_normalized_fixed_vector_of_nonzero_isSymmetricProjection
    {D : Type u} [NormedAddCommGroup D] [InnerProductSpace Complex D]
    [Semantics.FiniteQuantumSystem D]
    (P : Semantics.Operator D) (hP : P.IsSymmetricProjection) (hP0 : P ≠ 0) :
    ∃ eta : D, ‖eta‖ = 1 ∧ P eta = eta := by sorry
