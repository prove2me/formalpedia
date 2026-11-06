-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_conj_tensorMap_right
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_conj_tensorMap_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:02:47.710208+00:00
-- url     : https://prove2.me/theorems/cf85d0b9-5cb9-43c7-a592-12153f76deb9
-- title:
--   BPTCommuting Projector Model: isotypic Sector Block Transport Left conj tensor Map right
-- statement:
--   The active-sector block transport leaves a literal right exterior probe on
--   the right of the resulting `A tensor W` factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ExternalLocal.lean#L156-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ExternalLocal.lean#L156-L189

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_InternalResidual
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ExternalLocal
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_conj_tensorMap_right
    {A H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (Z : Semantics.Operator C) :
    (isotypicSectorBlockTransportLeft A H W N C U).conjOperator
        (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A H)) Z) =
      TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A W))
        (TensorProduct.map (1 : Semantics.Operator N) Z) := by sorry
