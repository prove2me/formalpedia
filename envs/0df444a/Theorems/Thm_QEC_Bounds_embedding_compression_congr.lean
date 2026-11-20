-- Prove2me | Theorems.Thm_QEC_Bounds_embedding_compression_congr
-- name    : QEC.Bounds.embedding_compression_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:48:54.046323+00:00
-- url     : https://prove2.me/theorems/59e9a3d7-eedf-46a3-8e4d-84be93f5155c
-- title:
--   Bounds: embedding compression congr
-- statement:
--   The Bounds construction uses the embedding compression congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L62-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L62-L70

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompressionRaw
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_CompressionAlgebra
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u

theorem QEC.Bounds.embedding_compression_congr
    {S K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (E : S →ₗ[Complex] K) {P Q : Semantics.Operator K} (h : P = Q) :
    (LinearMap.adjoint E).comp (P.comp E) =
      (LinearMap.adjoint E).comp (Q.comp E) := by sorry
