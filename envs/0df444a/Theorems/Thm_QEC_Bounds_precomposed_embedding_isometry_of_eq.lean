-- Prove2me | Theorems.Thm_QEC_Bounds_precomposed_embedding_isometry_of_eq
-- name    : QEC.Bounds.precomposed_embedding_isometry_of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:51:32.518334+00:00
-- url     : https://prove2.me/theorems/f97ed73b-5b7c-4a87-859a-9ffa2011f05b
-- title:
--   Bounds: precomposed embedding isometry of eq
-- statement:
--   The Bounds construction uses the precomposed embedding isometry of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L177-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L177-L199

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompressionRaw
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_CompressionAlgebra
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u
set_option maxHeartbeats 1000000

theorem QEC.Bounds.precomposed_embedding_isometry_of_eq
    {S H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport S H) (E : H →ₗ[Complex] K)
    (Enew : S →ₗ[Complex] K) (hEnew : Enew = E.comp U.toLinearEquiv.toLinearMap)
    (hE : (LinearMap.adjoint E).comp E = (1 : Semantics.Operator H)) :
    (LinearMap.adjoint Enew).comp Enew = (1 : Semantics.Operator S) := by sorry
