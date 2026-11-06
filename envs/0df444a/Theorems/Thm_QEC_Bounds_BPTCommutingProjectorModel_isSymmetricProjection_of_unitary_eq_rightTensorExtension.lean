-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_of_unitary_eq_rightTensorExtension
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_of_unitary_eq_rightTensorExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:21:59.163372+00:00
-- url     : https://prove2.me/theorems/9ff43b0e-9de3-47f5-ba75-ba6978369cf2
-- title:
--   BPTCommuting Projector Model: is Symmetric Projection of unitary eq right Tensor Extension
-- statement:
--   A unitary block equality with a right-tensor extension reflects projection structure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L272-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L272-L291

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Embedding
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_of_unitary_eq_rightTensorExtension
    {A H W N : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (P : Semantics.Operator (Semantics.CompositeSystem A H))
    (Pleft : Semantics.Operator (Semantics.CompositeSystem A W))
    (eta : N) (heta : ‖eta‖ = 1)
    (hP : P.IsSymmetricProjection)
    (hleft : (unitaryLTensor A U).conjOperator P =
      rightTensorExtensionAfterLeft A W N Pleft) :
    Pleft.IsSymmetricProjection := by sorry
