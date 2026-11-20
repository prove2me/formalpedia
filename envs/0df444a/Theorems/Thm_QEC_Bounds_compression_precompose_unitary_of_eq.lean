-- Prove2me | Theorems.Thm_QEC_Bounds_compression_precompose_unitary_of_eq
-- name    : QEC.Bounds.compression_precompose_unitary_of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:50:42.244193+00:00
-- url     : https://prove2.me/theorems/3df01b64-cc28-4138-8d94-48df8b194975
-- title:
--   Bounds: compression precompose unitary of eq
-- statement:
--   The Bounds construction uses the compression precompose unitary of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L49-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L49-L60

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompressionRaw
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_CompressionAlgebra
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u

theorem QEC.Bounds.compression_precompose_unitary_of_eq
    {S H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport S H) (J : H →ₗ[Complex] K)
    (Jnew : S →ₗ[Complex] K) (hJnew : Jnew = J.comp U.toLinearEquiv.toLinearMap)
    (P : Semantics.Operator K) :
    (LinearMap.adjoint Jnew).comp (P.comp Jnew) =
      U.symm.conjOperator ((LinearMap.adjoint J).comp (P.comp J)) := by sorry
