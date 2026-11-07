-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_comp_adjoint_eq_sum_rankOne_cross
-- name    : QEC.Bounds.BPTCommutingProjectorModel.comp_adjoint_eq_sum_rankOne_cross
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:29:26.787201+00:00
-- url     : https://prove2.me/theorems/3a28e051-3f05-4ab3-bce8-716a52ab86ef
-- title:
--   BPTCommuting Projector Model: comp adjoint eq sum rank One cross
-- statement:
--   The finite cross-Gram operator is the sum of paired rank-one columns.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L296-L311
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L296-L311

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_PartialTrace
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.comp_adjoint_eq_sum_rankOne_cross
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (b : OrthonormalBasis (Fin (Module.finrank Complex C)) Complex C)
    (A B : C →ₗ[Complex] N) :
    A.comp (LinearMap.adjoint B) = ∑ j,
      (InnerProductSpace.rankOne Complex (A (b j)) (B (b j))).toLinearMap := by sorry
