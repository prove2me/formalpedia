-- Prove2me | Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
-- name    : QEC.Semantics.UnitaryTransport.conjDensity_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:26.896247+00:00
-- url     : https://prove2.me/theorems/4d5bd37a-67d8-4cbc-a1fa-1ff8faee1eaa
-- title:
--   Unitary Transport: conj Density apply
-- statement:
--   The Unitary Transport construction uses the conj Density apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L842-L846
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L842-L846

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

theorem QEC.Semantics.UnitaryTransport.conjDensity_apply (U : UnitaryTransport H K)
    (rho : DensityOperator H) (x : K) :
    (U.conjDensity rho).toOperator x =
      U.toLinearEquiv (rho.toOperator (U.toLinearEquiv.symm x)) := by sorry

attribute [defeq] QEC.Semantics.UnitaryTransport.conjDensity_apply
