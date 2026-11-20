-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_compression_conjOperator_of_embedding_intertwines
-- name    : QEC.Bounds.BPTCommutingProjectorModel.compression_conjOperator_of_embedding_intertwines
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:17:02.930366+00:00
-- url     : https://prove2.me/theorems/2296d0a7-2041-4179-bb7d-854ab53696fd
-- title:
--   BPTCommuting Projector Model: compression conj Operator of embedding intertwines
-- statement:
--   Move an operator compression across an intertwining of an isometric lift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L161-L202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L161-L202

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open QEC.Bounds.BPTCommutingProjectorModel
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u

theorem QEC.Bounds.BPTCommutingProjectorModel.compression_conjOperator_of_embedding_intertwines
    {S H K : Type u} [NormedAddCommGroup S] [InnerProductSpace Complex S]
    [Semantics.FiniteQuantumSystem S] [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (embedding : S →ₗ[Complex] K) (V : Semantics.UnitaryTransport K K)
    (W : Semantics.UnitaryTransport S S) (P : Semantics.Operator K)
    (hintertwines : V.toLinearEquiv.toLinearMap.comp embedding =
      embedding.comp W.toLinearEquiv.toLinearMap) :
    (LinearMap.adjoint embedding).comp ((V.conjOperator P).comp embedding) =
      W.conjOperator ((LinearMap.adjoint embedding).comp (P.comp embedding)) := by sorry
