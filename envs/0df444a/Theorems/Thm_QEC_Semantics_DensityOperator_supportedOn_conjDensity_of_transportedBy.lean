-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_conjDensity_of_transportedBy
-- name    : QEC.Semantics.DensityOperator.supportedOn_conjDensity_of_transportedBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:55.486206+00:00
-- url     : https://prove2.me/theorems/fca5935a-b227-4cb4-bed2-96079ecc58ff
-- title:
--   Density Operator: supported On conj Density of transported By
-- statement:
--   The Density Operator construction uses the supported On conj Density of transported By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L894-L902
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L894-L902

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

theorem QEC.Semantics.DensityOperator.supportedOn_conjDensity_of_transportedBy
    (U : UnitaryTransport H K) {C : QuantumCode H} {D : QuantumCode K}
    {rho : DensityOperator H} (hCD : QuantumCode.TransportedBy U C D)
    (hρ : SupportedOn C rho) :
    SupportedOn D (U.conjDensity rho) := by sorry
