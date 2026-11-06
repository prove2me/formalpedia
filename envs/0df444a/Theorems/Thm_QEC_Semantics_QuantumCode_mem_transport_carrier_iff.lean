-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumCode_mem_transport_carrier_iff
-- name    : QEC.Semantics.QuantumCode.mem_transport_carrier_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:45.247206+00:00
-- url     : https://prove2.me/theorems/bccad034-4fca-4a28-9fb8-acac1ff5c21c
-- title:
--   Quantum Code: mem transport carrier iff
-- statement:
--   The Quantum Code construction uses the mem transport carrier iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L875-L879
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L875-L879

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.QuantumCode
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]

theorem QEC.Semantics.QuantumCode.mem_transport_carrier_iff (U : UnitaryTransport H K) (C : QuantumCode H)
    {x : H} :
    U.toLinearEquiv x ∈ (C.transport U).carrier ↔ x ∈ C.carrier := by sorry
