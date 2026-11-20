-- Prove2me | Theorems.Thm_QEC_Bounds_compression_conj_after_transportPair
-- name    : QEC.Bounds.compression_conj_after_transportPair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:28:02.936185+00:00
-- url     : https://prove2.me/theorems/1ab009cc-27cb-422a-ba11-e2a8a1c04fe7
-- title:
--   Bounds: compression conj after transport Pair
-- statement:
--   Compressing through an outer transport and an inner coordinate transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/SelectedTensorCore.lean#L45-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/SelectedTensorCore.lean#L45-L73

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Coordinates
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_SelectedTensorCore
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u v
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 50000

theorem QEC.Bounds.compression_conj_after_transportPair
    {S T H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup T] [InnerProductSpace Complex T] [Semantics.FiniteQuantumSystem T]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (outer : Semantics.UnitaryTransport H K) (coordinates : Semantics.UnitaryTransport H T)
    (embedding : S →ₗ[Complex] T) (P : Semantics.Operator H) :
    (LinearMap.adjoint (outer.toLinearEquiv.toLinearMap.comp
      (coordinates.symm.toLinearEquiv.toLinearMap.comp embedding))).comp
        ((outer.conjOperator P).comp
          (outer.toLinearEquiv.toLinearMap.comp
            (coordinates.symm.toLinearEquiv.toLinearMap.comp embedding))) =
      (LinearMap.adjoint embedding).comp
        ((coordinates.conjOperator P).comp embedding) := by sorry
