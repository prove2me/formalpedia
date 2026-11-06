-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_symm_conjDensity_transport_iff
-- name    : QEC.Semantics.DensityOperator.supportedOn_symm_conjDensity_transport_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:51.75996+00:00
-- url     : https://prove2.me/theorems/273c93ea-16b8-4d91-919b-ce7b7a8f53d7
-- title:
--   Density Operator: supported On symm conj Density transport iff
-- statement:
--   The Density Operator construction uses the supported On symm conj Density transport iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L920-L933
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L920-L933

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

theorem QEC.Semantics.DensityOperator.supportedOn_symm_conjDensity_transport_iff
    (U : UnitaryTransport H K) (C : QuantumCode H) (rho : DensityOperator K) :
    SupportedOn C (U.symm.conjDensity rho) ↔ SupportedOn (C.transport U) rho := by sorry
