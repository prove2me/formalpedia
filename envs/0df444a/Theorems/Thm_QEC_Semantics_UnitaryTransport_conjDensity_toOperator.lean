-- Prove2me | Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
-- name    : QEC.Semantics.UnitaryTransport.conjDensity_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:19.062787+00:00
-- url     : https://prove2.me/theorems/8a12d3dc-5fbd-472b-8255-dd42b9be5bf1
-- title:
--   Unitary Transport: conj Density to Operator
-- statement:
--   The Unitary Transport construction uses the conj Density to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L826-L829
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L826-L829

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

theorem QEC.Semantics.UnitaryTransport.conjDensity_toOperator (U : UnitaryTransport H K)
    (rho : DensityOperator H) :
    (U.conjDensity rho).toOperator = U.conjOperator rho.toOperator := by sorry

attribute [defeq] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
