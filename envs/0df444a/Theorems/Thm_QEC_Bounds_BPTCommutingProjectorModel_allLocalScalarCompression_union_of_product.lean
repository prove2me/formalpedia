-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_allLocalScalarCompression_union_of_product
-- name    : QEC.Bounds.BPTCommutingProjectorModel.allLocalScalarCompression_union_of_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:38:18.854488+00:00
-- url     : https://prove2.me/theorems/91952806-c4aa-461e-b597-caf3d95f24e5
-- title:
--   BPTCommuting Projector Model: all Local Scalar Compression union of product
-- statement:
--   Scalar compression for all products of separated local operators extends to
--   all local operators on their concrete union by finite matrix-unit expansion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorization.lean#L532-L547
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorization.lean#L532-L547

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Support
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorization
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.allLocalScalarCompression_union_of_product
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right)
    (hproduct : ∀ (A : Semantics.Operator (M.regionSubsystem left).selectedSystem)
      (B : Semantics.Operator (M.regionSubsystem right).selectedSystem),
      Semantics.QuditSubsystem.ScalarCompression M.codeSpace
        ((M.regionSubsystem left).extendLocalToRegister A *
          (M.regionSubsystem right).extendLocalToRegister B)) :
    Semantics.QuditSubsystem.AllLocalScalarCompression M.codeSpace
      (M.regionSubsystem (left ∪ right)) := by sorry
