-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryTransport_conj_compression_of_intertwines
-- name    : QEC.Bounds.BPTCommutingProjectorModel.unitaryTransport_conj_compression_of_intertwines
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:22:16.107146+00:00
-- url     : https://prove2.me/theorems/4436bf8f-5e52-4987-b1b4-b0b2b9652f0f
-- title:
--   BPTCommuting Projector Model: unitary Transport conj compression of intertwines
-- statement:
--   Conjugating a compression across an actual intertwining square is the same as
--   compressing the conjugated operator in the transported subspace coordinates.
--   This is the generic bridge from a BV03 block equality to the later sequential
--   `B`/`C` sector compression; neither compressed block is assumed as input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/BlockTransport.lean#L275-L322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/BlockTransport.lean#L275-L322

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_BlockTransport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.unitaryTransport_conj_compression_of_intertwines
    {H H' S S' : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup H'] [InnerProductSpace Complex H'] [Semantics.FiniteQuantumSystem H']
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup S'] [InnerProductSpace Complex S'] [Semantics.FiniteQuantumSystem S']
    (T : Semantics.UnitaryTransport H H') (Tsub : Semantics.UnitaryTransport S S')
    (K : S →ₗ[Complex] H) (K' : S' →ₗ[Complex] H')
    (hintertwines : T.toLinearEquiv.toLinearMap.comp K = K'.comp Tsub.toLinearEquiv.toLinearMap)
    (R : Semantics.Operator H) :
    Tsub.conjOperator ((LinearMap.adjoint K).comp (R.comp K)) =
      (LinearMap.adjoint K').comp ((T.conjOperator R).comp K') := by sorry
