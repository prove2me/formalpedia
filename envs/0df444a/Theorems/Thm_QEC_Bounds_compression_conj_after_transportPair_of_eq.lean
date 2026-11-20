-- Prove2me | Theorems.Thm_QEC_Bounds_compression_conj_after_transportPair_of_eq
-- name    : QEC.Bounds.compression_conj_after_transportPair_of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:29:06.074288+00:00
-- url     : https://prove2.me/theorems/728c9136-c922-4e21-b7cc-36d189abacaf
-- title:
--   Bounds: compression conj after transport Pair of eq
-- statement:
--   Reuse a named output-coordinate equality before compressing through two transports.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/SelectedTensorCore.lean#L76-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/SelectedTensorCore.lean#L76-L90

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Coordinates
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_SelectedTensorCore
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u v

theorem QEC.Bounds.compression_conj_after_transportPair_of_eq
    {S T H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup T] [InnerProductSpace Complex T] [Semantics.FiniteQuantumSystem T]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (outer : Semantics.UnitaryTransport H K) (coordinates : Semantics.UnitaryTransport H T)
    (embedding : S →ₗ[Complex] T) (outputEmbedding : S →ₗ[Complex] K)
    (P : Semantics.Operator H)
    (houtput : outputEmbedding = outer.toLinearEquiv.toLinearMap.comp
      (coordinates.symm.toLinearEquiv.toLinearMap.comp embedding)) :
    (LinearMap.adjoint outputEmbedding).comp ((outer.conjOperator P).comp outputEmbedding) =
      (LinearMap.adjoint embedding).comp ((coordinates.conjOperator P).comp embedding) := by sorry
