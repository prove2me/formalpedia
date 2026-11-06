-- Prove2me | Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_trace
-- name    : QEC.Semantics.UnitaryTransport.conjDensity_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:36:31.221492+00:00
-- url     : https://prove2.me/theorems/0a3d43d2-65dc-451a-b13c-9aa5d73c9ae3
-- title:
--   Unitary Transport: conj Density trace
-- statement:
--   The Unitary Transport construction uses the conj Density trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L831-L834
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L831-L834

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

theorem QEC.Semantics.UnitaryTransport.conjDensity_trace (U : UnitaryTransport H K)
    (rho : DensityOperator H) :
    LinearMap.trace Complex K (U.conjDensity rho).toOperator = 1 := by sorry
