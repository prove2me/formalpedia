-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_conj_overlapLiftLeft_middle
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_conj_overlapLiftLeft_middle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:57:56.809203+00:00
-- url     : https://prove2.me/theorems/69898f77-6ad5-4235-a0d1-472356ec79ea
-- title:
--   BPTCommuting Projector Model: isotypic Sector Block Transport Left conj overlap Lift Left middle
-- statement:
--   The common isotypic block transport also carries an operator on the residual
--   multiplicity factor to the literal `N tensor C` right block.  It is the
--   operator-level transport used to pass hM no-information from `B` to `B''`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/InternalResidual.lean#L28-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/InternalResidual.lean#L28-L56

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_RankOneTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_InternalResidual
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_conj_overlapLiftLeft_middle
    {A H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (E : Semantics.Operator (Semantics.CompositeSystem A H))
    (X : Semantics.Operator N)
    (hE : (unitaryLTensor A U).conjOperator E =
      TensorProduct.map (1 : Semantics.Operator A)
        (TensorProduct.map (1 : Semantics.Operator W) X)) :
    (isotypicSectorBlockTransportLeft A H W N C U).conjOperator
        (overlapLiftLeft (C := C) E) =
      TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A W))
        (TensorProduct.map X (1 : Semantics.Operator C)) := by sorry
