-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_compression_conjOperator_comp_unitary
-- name    : QEC.Bounds.BPTCommutingProjectorModel.compression_conjOperator_comp_unitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-18T04:12:48.951193+00:00
-- url     : https://prove2.me/theorems/759a000a-5989-4e22-9a83-dca2c643a9a6
-- title:
--   BPTCommuting Projector Model: compression conj Operator comp unitary
-- statement:
--   Compressing a conjugated operator through the transported embedding changes no block data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L433-L446
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L433-L446

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.compression_conjOperator_comp_unitary
    {S H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (J : S →ₗ[Complex] H)
    (P : Semantics.Operator H) :
    (LinearMap.adjoint (U.toLinearEquiv.toLinearMap.comp J)).comp
        ((U.conjOperator P).comp (U.toLinearEquiv.toLinearMap.comp J)) =
      (LinearMap.adjoint J).comp (P.comp J) := by sorry
