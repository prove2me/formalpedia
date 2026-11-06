-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_associator_coherence
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_associator_coherence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:29:28.575273+00:00
-- url     : https://prove2.me/theorems/bd865887-30e1-4c1f-b704-2b7d51c2c84b
-- title:
--   BPTCommuting Projector Model: isotypic Sector Block Transport Left associator coherence
-- statement:
--   The associator route inside the common left block coordinate is the canonical
--   reassociation `((A tensor W) tensor N) tensor C -> (A tensor W) tensor (N tensor C)`.
--   This supplies the literal tensor-map equality rather than relying on a
--   definitional associativity reduction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Transport.lean#L109-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Transport.lean#L109-L148

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Embedding
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Transport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_associator_coherence
    (A W N C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C] :
    composeUnitaryTransport
      (composeUnitaryTransport
        (composeUnitaryTransport
          (unitaryRTensor (tensorAssociatorUnitary A W N) C)
          (tensorAssociatorUnitary A (Semantics.CompositeSystem W N) C))
        (unitaryLTensor A (tensorAssociatorUnitary W N C)))
      (tensorAssociatorUnitary A W (Semantics.CompositeSystem N C)).symm =
      tensorAssociatorUnitary (Semantics.CompositeSystem A W) N C := by sorry
