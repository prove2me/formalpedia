-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_conj_overlap_product
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_conj_overlap_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:34:05.569765+00:00
-- url     : https://prove2.me/theorems/6d30cebd-e98f-4601-8f9a-a97a76dc4f35
-- title:
--   BPTCommuting Projector Model: isotypic Sector Block Transport Left conj overlap product
-- statement:
--   One active BV03 sector has the actual source tensor-block product under its
--   single coherent boundary unitary.  This combines the two preceding projector
--   equalities and is the block equality consumed by the first physical cut.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Conjugation.lean#L133-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Conjugation.lean#L133-L156

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_conj_overlap_product
    {A H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (P : Semantics.Operator (Semantics.CompositeSystem A H))
    (Q : Semantics.Operator (Semantics.CompositeSystem H C))
    (Pleft : Semantics.Operator (Semantics.CompositeSystem A W))
    (Qright : Semantics.Operator (Semantics.CompositeSystem N C))
    (hleft : (unitaryLTensor A U).conjOperator P =
      rightTensorExtensionAfterLeft A W N Pleft)
    (hright : (unitaryRTensor U C).conjOperator Q =
      leftTensorExtensionBeforeRight W N C Qright) :
    (isotypicSectorBlockTransportLeft A H W N C U).conjOperator
        (overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q) =
      TensorProduct.map Pleft Qright := by sorry
