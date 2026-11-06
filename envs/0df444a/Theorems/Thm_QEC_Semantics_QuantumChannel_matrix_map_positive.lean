-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumChannel_matrix_map_positive
-- name    : QEC.Semantics.QuantumChannel.matrix_map_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:35:45.283196+00:00
-- url     : https://prove2.me/theorems/1cba259e-b8cd-4cc5-aa23-d13a5a038f5c
-- title:
--   Quantum Channel: matrix map positive
-- statement:
--   The Quantum Channel construction uses the matrix map positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L232-L235
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L232-L235

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.QuantumChannel
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]

theorem QEC.Semantics.QuantumChannel.matrix_map_positive (Φ : QuantumChannel H K) (n : Nat) (M : OperatorMatrix n H)
    (hM : OperatorMatrix.IsPositive M) :
    OperatorMatrix.IsPositive (OperatorMatrix.map Φ.toLinearMap M) := by sorry
