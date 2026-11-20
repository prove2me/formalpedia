-- Prove2me | Theorems.Thm_QEC_Bounds_unitary_conjOperator_congr
-- name    : QEC.Bounds.unitary_conjOperator_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:50:14.476189+00:00
-- url     : https://prove2.me/theorems/c5a29a6c-6660-40e3-b77d-76a68f5c6024
-- title:
--   Bounds: unitary conj Operator congr
-- statement:
--   The Bounds construction uses the unitary conj Operator congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L168-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L168-L174

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompressionRaw
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_CompressionAlgebra
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u

theorem QEC.Bounds.unitary_conjOperator_congr
    {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    (U : Semantics.UnitaryTransport H H) {P Q : Semantics.Operator H} (h : P = Q) :
    U.conjOperator P = U.conjOperator Q := by sorry
