-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_comp_tensorMap_right
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_comp_tensorMap_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:30:03.232415+00:00
-- url     : https://prove2.me/theorems/b528877b-6645-4bd6-8a2b-02d15a716f97
-- title:
--   BPTCommuting Projector Model: isotypic Sector Block Transport Left comp tensor Map right
-- statement:
--   The coherent `B`-sector block transport is natural for a literal map on its
--   untouched exterior factor.  In particular, a later `C`-sector compression can
--   be moved across the `B` coordinate transport without postulating a common
--   block equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/BlockTransport.lean#L29-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/BlockTransport.lean#L29-L138

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_comp_tensorMap_right
    {A H W N C C' : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup C'] [InnerProductSpace Complex C'] [Semantics.FiniteQuantumSystem C']
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (K : C →ₗ[Complex] C') :
    (isotypicSectorBlockTransportLeft A H W N C' U).toLinearEquiv.toLinearMap.comp
        (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A H)) K) =
      (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A W))
        (TensorProduct.map (1 : Semantics.Operator N) K)).comp
        (isotypicSectorBlockTransportLeft A H W N C U).toLinearEquiv.toLinearMap := by sorry
