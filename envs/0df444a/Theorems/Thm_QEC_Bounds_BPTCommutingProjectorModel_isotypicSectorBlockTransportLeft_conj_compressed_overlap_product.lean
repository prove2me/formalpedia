-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_conj_compressed_overlap_product
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_conj_compressed_overlap_product
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:22:18.805768+00:00
-- url     : https://prove2.me/theorems/7126fbb6-0c3b-4ca7-9678-dc8c493a0071
-- title:
--   BPTCommuting Projector Model: isotypic Sector Block Transport Left conj compressed overlap product
-- statement:
--   Compression to a chosen BV03 isotypic sector and its common block transport
--   commute.  This is the generic form used by both physical BPT cuts: it turns
--   the actual compressed overlap product, not merely its individual factors,
--   into `P_left tensor Q_right`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Conjugation.lean#L164-L198
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Conjugation.lean#L164-L198

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Conjugation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_conj_compressed_overlap_product
    {A H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A H))
    (Q : Semantics.Operator (Semantics.CompositeSystem H C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) H)
    (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (Semantics.CompositeSystem W N))
    (Pleft : Semantics.Operator (Semantics.CompositeSystem A W))
    (Qright : Semantics.Operator (Semantics.CompositeSystem N C))
    (hleft : (unitaryLTensor A U).conjOperator
        (overlapProjectorOnIsotypicComponent P component) =
      rightTensorExtensionAfterLeft A W N Pleft)
    (hright : (unitaryRTensor U C).conjOperator
        (overlapRightProjectorOnIsotypicComponent P Q component) =
      leftTensorExtensionBeforeRight W N C Qright) :
    (isotypicSectorBlockTransportLeft A (component.1.restrictScalars Complex) W N C U).conjOperator
        ((LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C)
          (component.1.restrictScalars Complex))).comp
          ((overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q).comp
            (tensorTripleSubtypeEmbedding (A := A) (C := C)
              (component.1.restrictScalars Complex)))) =
      TensorProduct.map Pleft Qright := by sorry
