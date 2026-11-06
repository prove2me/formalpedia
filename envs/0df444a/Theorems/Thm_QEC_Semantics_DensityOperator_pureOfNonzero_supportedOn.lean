-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_supportedOn
-- name    : QEC.Semantics.DensityOperator.pureOfNonzero_supportedOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:02:07.351128+00:00
-- url     : https://prove2.me/theorems/b9df50fa-6a3c-4481-9d45-d00f3a2a4c98
-- title:
--   Density Operator: pure Of Nonzero supported On
-- statement:
--   The Density Operator construction uses the pure Of Nonzero supported On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L102-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean#L102-L106

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.DensityOperator.pureOfNonzero_supportedOn {C : QuantumCode H} {x : H} (hx : x ≠ 0)
    (hxC : x ∈ C.carrier) : SupportedOn C (pureOfNonzero x hx) := by sorry
