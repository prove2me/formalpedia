-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_compression_precompose_unitary
-- name    : QEC.Bounds.BPTCommutingProjectorModel.compression_precompose_unitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:14:24.95329+00:00
-- url     : https://prove2.me/theorems/d0a9fb4c-76af-457e-a055-7f9873adc438
-- title:
--   BPTCommuting Projector Model: compression precompose unitary
-- statement:
--   Precomposing an embedding by a unitary conjugates its compressed operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L146-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L146-L158

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

theorem QEC.Bounds.BPTCommutingProjectorModel.compression_precompose_unitary
    {S H K : Type u} [NormedAddCommGroup S] [InnerProductSpace Complex S]
    [Semantics.FiniteQuantumSystem S] [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport S H) (J : H →ₗ[Complex] K)
    (P : Semantics.Operator K) :
    (LinearMap.adjoint (J.comp U.toLinearEquiv.toLinearMap)).comp
        (P.comp (J.comp U.toLinearEquiv.toLinearMap)) =
      U.symm.conjOperator ((LinearMap.adjoint J).comp (P.comp J)) := by sorry
