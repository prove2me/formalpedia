-- Prove2me | Theorems.Thm_QEC_Semantics_UnitaryTransport_conjOperator_comp
-- name    : QEC.Semantics.UnitaryTransport.conjOperator_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:21:02.950827+00:00
-- url     : https://prove2.me/theorems/8e782803-a354-43b3-b4c4-782cc3449696
-- title:
--   Unitary Transport: conj Operator comp
-- statement:
--   The Unitary Transport construction uses the conj Operator comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L789-L792
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L789-L792

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.UnitaryTransport
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]

theorem QEC.Semantics.UnitaryTransport.conjOperator_comp (U : UnitaryTransport H K) (A B : Operator H) :
    U.conjOperator (A.comp B) = (U.conjOperator A).comp (U.conjOperator B) := by sorry
