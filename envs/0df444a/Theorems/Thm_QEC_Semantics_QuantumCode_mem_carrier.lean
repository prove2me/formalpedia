-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumCode_mem_carrier
-- name    : QEC.Semantics.QuantumCode.mem_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:54.962821+00:00
-- url     : https://prove2.me/theorems/792f8879-91d3-400f-bc28-cfd5e4bbbc23
-- title:
--   Quantum Code: mem carrier
-- statement:
--   The Quantum Code construction uses the mem carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L645-L647
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L645-L647

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.QuantumCode
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.QuantumCode.mem_carrier (C : QuantumCode H) {v : H} :
    v ∈ C.carrier ↔ v ∈ (C : Submodule Complex H) := by sorry
