-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumCode_transportedBy_transport
-- name    : QEC.Semantics.QuantumCode.transportedBy_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:53.854535+00:00
-- url     : https://prove2.me/theorems/4655f67a-2279-4617-9289-0351293eae41
-- title:
--   Quantum Code: transported By transport
-- statement:
--   The Quantum Code construction uses the transported By transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L881-L884
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L881-L884

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

theorem QEC.Semantics.QuantumCode.transportedBy_transport (U : UnitaryTransport H K) (C : QuantumCode H) :
    TransportedBy U C (C.transport U) := by sorry
