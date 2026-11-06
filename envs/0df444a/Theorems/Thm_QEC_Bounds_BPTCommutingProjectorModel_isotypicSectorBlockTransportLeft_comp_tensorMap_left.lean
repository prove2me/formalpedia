-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_comp_tensorMap_left
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_comp_tensorMap_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:29:33.183311+00:00
-- url     : https://prove2.me/theorems/270fcfdc-3f8f-4b3e-a99b-b2b5e8b590a1
-- title:
--   BPTCommuting Projector Model: isotypic Sector Block Transport Left comp tensor Map left
-- statement:
--   The coherent isotypic block transport is also natural for a map on its left
--   ambient factor.  In the BPT application this transports the active `B`
--   subtype embedding through the first-cut `C` block, so the first sequential
--   compression is derived from the actual BV03 equation rather than supplied as
--   an `hfirst` hypothesis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/BlockTransport.lean#L147-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/BlockTransport.lean#L147-L203

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_comp_tensorMap_left
    {A A' H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup A'] [InnerProductSpace Complex A'] [Semantics.FiniteQuantumSystem A']
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (K : A →ₗ[Complex] A') :
    (isotypicSectorBlockTransportLeft A' H W N C U).toLinearEquiv.toLinearMap.comp
        (TensorProduct.map (TensorProduct.map K (1 : Semantics.Operator H))
          (1 : Semantics.Operator C)) =
      (TensorProduct.map (TensorProduct.map K (1 : Semantics.Operator W))
        (1 : Semantics.Operator (Semantics.CompositeSystem N C))).comp
        (isotypicSectorBlockTransportLeft A H W N C U).toLinearEquiv.toLinearMap := by sorry
