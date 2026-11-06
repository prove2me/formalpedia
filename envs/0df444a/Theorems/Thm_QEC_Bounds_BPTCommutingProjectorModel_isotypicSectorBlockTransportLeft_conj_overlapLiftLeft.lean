-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_conj_overlapLiftLeft
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_conj_overlapLiftLeft
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:22:16.971392+00:00
-- url     : https://prove2.me/theorems/f27d18bc-16c0-4e6f-8504-e46aa540b388
-- title:
--   BPTCommuting Projector Model: isotypic Sector Block Transport Left conj overlap Lift Left
-- statement:
--   The common four-factor coordinate sends the left projector of one BV03 block
--   to its literal source factor `P_left tensor 1`.  This is the first half of the
--   block projector equality used below for the physical first cut.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Conjugation.lean#L28-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Conjugation.lean#L28-L74

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_conj_overlapLiftLeft
    {A H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (P : Semantics.Operator (Semantics.CompositeSystem A H))
    (Pleft : Semantics.Operator (Semantics.CompositeSystem A W))
    (hleft : (unitaryLTensor A U).conjOperator P =
      rightTensorExtensionAfterLeft A W N Pleft) :
    (isotypicSectorBlockTransportLeft A H W N C U).conjOperator
        (overlapLiftLeft (C := C) P) =
      TensorProduct.map Pleft
        (1 : Semantics.Operator (Semantics.CompositeSystem N C)) := by sorry
