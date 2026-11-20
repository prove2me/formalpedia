-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_reassociated_isometric_lift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.reassociated_isometric_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:45.040447+00:00
-- url     : https://prove2.me/theorems/b8e19130-ae4f-4bc4-b68a-1afa3097a37b
-- title:
--   BPTCommuting Projector Model: reassociated isometric lift
-- statement:
--   Reassociate an isometric lift together with its compressed projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L237-L251
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L237-L251

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

theorem QEC.Bounds.BPTCommutingProjectorModel.reassociated_isometric_lift
    {H K X : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    (T : Semantics.UnitaryTransport H K) (embedding : K →ₗ[Complex] X)
    (P : Semantics.Operator K) :
    let reassociatedEmbedding := embedding.comp T.toLinearEquiv.toLinearMap
    reassociatedEmbedding.comp
        ((T.symm.conjOperator P).comp (LinearMap.adjoint reassociatedEmbedding)) =
      embedding.comp (P.comp (LinearMap.adjoint embedding)) := by sorry
