-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_eq_right
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_eq_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:29:17.903124+00:00
-- url     : https://prove2.me/theorems/0ae082ee-0dff-49d2-95d5-881b74ee88e9
-- title:
--   BPTCommuting Projector Model: isotypic Sector Block Transport Left eq right
-- statement:
--   The two concrete routes through an isotypic block agree.  This is the needed
--   four-factor associator coherence, proved on tensor generators rather than
--   assumed as a coherence axiom.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Transport.lean#L77-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Transport.lean#L77-L101

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_eq_right
    (A H W N C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N)) :
    isotypicSectorBlockTransportLeft A H W N C U =
      isotypicSectorBlockTransportRight A H W N C U := by sorry
