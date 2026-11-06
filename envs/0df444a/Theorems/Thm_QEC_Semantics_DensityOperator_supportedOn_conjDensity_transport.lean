-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_conjDensity_transport
-- name    : QEC.Semantics.DensityOperator.supportedOn_conjDensity_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:40.275213+00:00
-- url     : https://prove2.me/theorems/227c6ac9-1ec6-4412-b022-7d52b5bf8f5c
-- title:
--   Density Operator: supported On conj Density transport
-- statement:
--   The Density Operator construction uses the supported On conj Density transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L904-L908
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L904-L908

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.DensityOperator
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]

theorem QEC.Semantics.DensityOperator.supportedOn_conjDensity_transport
    (U : UnitaryTransport H K) (C : QuantumCode H) (rho : DensityOperator H)
    (hρ : SupportedOn C rho) :
    SupportedOn (C.transport U) (U.conjDensity rho) := by sorry
