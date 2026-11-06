-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_conj_overlapLiftRight
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_conj_overlapLiftRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:35:17.630764+00:00
-- url     : https://prove2.me/theorems/14145a9c-0a29-4259-a3bd-f21c8820031e
-- title:
--   BPTCommuting Projector Model: isotypic Sector Block Transport Left conj overlap Lift Right
-- statement:
--   The same common coordinate sends the right projector of a BV03 block to its
--   literal source factor `1 tensor Q_right`.  The proof uses the right transport
--   route and then the already proved route coherence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Conjugation.lean#L81-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Conjugation.lean#L81-L126

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_conj_overlapLiftRight
    {A H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (Q : Semantics.Operator (Semantics.CompositeSystem H C))
    (Qright : Semantics.Operator (Semantics.CompositeSystem N C))
    (hright : (unitaryRTensor U C).conjOperator Q =
      leftTensorExtensionBeforeRight W N C Qright) :
    (isotypicSectorBlockTransportLeft A H W N C U).conjOperator
        (overlapLiftRight (A := A) Q) =
      TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A W)) Qright := by sorry
