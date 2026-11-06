-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumCode_mem_transport_carrier_iff_symm
-- name    : QEC.Semantics.QuantumCode.mem_transport_carrier_iff_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:35.049167+00:00
-- url     : https://prove2.me/theorems/e0e224f7-7524-4fc7-ac0c-f177333931ef
-- title:
--   Quantum Code: mem transport carrier iff symm
-- statement:
--   The Quantum Code construction uses the mem transport carrier iff symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L865-L873
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L865-L873

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

theorem QEC.Semantics.QuantumCode.mem_transport_carrier_iff_symm (U : UnitaryTransport H K) (C : QuantumCode H)
    {y : K} :
    y ∈ (C.transport U).carrier ↔ U.toLinearEquiv.symm y ∈ C.carrier := by sorry
